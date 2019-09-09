//! The LLVM backend for the Opus compiler.

use llvm_sys::*;
use llvm_sys::core::*;
use llvm_sys::prelude::*;
use llvm_sys::target::*;
use llvm_sys::target_machine::*;
use std::io;
use std::collections::HashMap;
use std::ffi::CString;
use crate::compile::{Compiler, TypeId, Type, Function, FunctionId, GlobalId, PointerType, CastType, Value};
use crate::generate_ir::{IrGenerator, Instruction};
use super::Backend;

pub struct LlvmBackend<'source> {
    compiler: &'source Compiler<'source>,
    context: LLVMContextRef,
    pub module: LLVMModuleRef,
    builder: LLVMBuilderRef,

    null_type: LLVMTypeRef,
    string_type: LLVMTypeRef,

    function_map: HashMap<FunctionId, LLVMValueRef>,
    global_map: HashMap<GlobalId, LLVMValueRef>, // FIXME: should this be a Vec instead?
}

impl<'source> Drop for LlvmBackend<'source> {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeBuilder(self.builder);
            LLVMDisposeModule(self.module);
            LLVMContextDispose(self.context);
        }
    }
}

impl<'source> LlvmBackend<'source> {
    pub fn new(compiler: &'source Compiler<'source>) -> Self {
        unsafe {
            let context = LLVMContextCreate();
            let module = LLVMModuleCreateWithName(b"main\0".as_ptr() as *const _);
            let builder = LLVMCreateBuilderInContext(context);

            let mut field_typerefs = vec![];
            let null_type = LLVMStructType(field_typerefs.as_mut_ptr(), field_typerefs.len() as _, 0);

            // FIXME: len should be a size_t-like type
            let mut field_typerefs = vec![LLVMPointerType(LLVMInt8TypeInContext(context), 0), LLVMInt64TypeInContext(context)];
            let string_type = LLVMStructType(field_typerefs.as_mut_ptr(), field_typerefs.len() as _, 0);

            LlvmBackend {
                compiler,
                context,
                module,
                builder,

                null_type,
                string_type,

                function_map: HashMap::new(),
                global_map: HashMap::new(),
            }
        }
    }

    fn translate_type(&self, typ: TypeId) -> LLVMTypeRef {
        unsafe {
            match *self.compiler.get_type_info(typ) {
                Type::Natural8 | Type::Integer8 => LLVMInt8TypeInContext(self.context),
                Type::Natural16 | Type::Integer16 => LLVMInt16TypeInContext(self.context),
                Type::Natural32 | Type::Integer32 => LLVMInt32TypeInContext(self.context),
                Type::Natural64 | Type::Integer64 => LLVMInt64TypeInContext(self.context),
                Type::Size | Type::Offset => LLVMInt64TypeInContext(self.context), // FIXME: should be target-dependent
                Type::Generic | Type::GenericInteger => unreachable!(),
                Type::Float32 => LLVMFloatTypeInContext(self.context),
                Type::Float64 => LLVMDoubleTypeInContext(self.context),
                Type::Null => self.null_type,
                Type::Bool => LLVMInt1TypeInContext(self.context),
                Type::String => self.string_type,
                Type::Pointer(_, subtype) => LLVMPointerType(self.translate_type(subtype), 0),
                Type::Record(ref fields) => {
                    let mut field_typerefs = vec![];
                    for &(_, type_id) in fields.iter() {
                        field_typerefs.push(self.translate_type(type_id));
                    }
                    LLVMStructType(field_typerefs.as_mut_ptr(), field_typerefs.len() as _, 0)
                },
                Type::Function { ref argument_types, return_type } => {
                    let return_typeref = self.translate_type(return_type);
                    let mut param_typerefs: Vec<LLVMTypeRef> = argument_types.iter().map(|&x| self.translate_type(x)).collect();
                    let function_type = LLVMFunctionType(return_typeref, param_typerefs.as_mut_ptr(), param_typerefs.len() as _, 0);
                    LLVMPointerType(function_type, 0)
                },
                Type::Array(size, subtype) => LLVMArrayType(self.translate_type(subtype), size as _),
                Type::Error => unreachable!(),
            }
        }
    }

    fn translate_value(&mut self, llvm_type: LLVMTypeRef, typ: TypeId, value: &Value) -> LLVMValueRef {
        unsafe {
            match *value {
                Value::Integer(i) => {
                    LLVMConstInt(llvm_type, i as _, self.compiler.type_is_signed(typ) as _)
                },
                Value::None => {
                    LLVMGetUndef(llvm_type)
                },
                Value::Error => unreachable!(),
            }
        }
    }

    pub fn add_global(&mut self, global_id: GlobalId, typ: TypeId, value: &Value) {
        let llvm_type = self.translate_type(typ);

        unsafe {
            let mut global_value = self.translate_value(llvm_type, typ, value);
            if !self.compiler.global_is_constant[global_id] {
                let llvm_value = global_value;
                global_value = LLVMAddGlobal(self.module, llvm_type, b"\0".as_ptr() as *const _);
                LLVMSetInitializer(global_value, llvm_value);
            }
            self.global_map.insert(global_id, global_value);
        }
    }

    fn mangle_symbol(&self, x: &str) -> String {
        format!("{}", match x {
            "+" => "Plus",
            "-" => "Minus",
            "*" => "Times",
            "/" => "Divide",
            "%" => "Modulo",
            "=" => "Equals",
            "<" => "LessThan",
            ">" => "GreaterThan",
            "<=" => "LessThanEquals",
            ">=" => "GreaterThanEquals",
            _ => x,
        })
    }

    fn mangle_function_name(&self, function: &Function) -> CString {
        if function.is_extern {
            CString::new(format!("{}", &function.name[0].as_ref().unwrap()[1..])).unwrap()
        } else {
            let mut output = String::new();
            output += "_opus";

            let mut i = 0;
            for part in function.name.iter() {
                match *part {
                    Some(ref x) => {
                        output += "_";
                        output += &*self.mangle_symbol(x);
                    },
                    None => {
                        output += "__";
                        output += &*self.mangle_type_name(function.arguments[i]);
                        i += 1;
                    },
                }
            }

            CString::new(output).unwrap()
        }
    }

    fn mangle_type_name(&self, typ: TypeId) -> String {
        let type_info = self.compiler.get_type_info(typ);
        match *type_info {
            Type::Integer8 => "int8".into(),
            Type::Integer16 => "int16".into(),
            Type::Integer32 => "int32".into(),
            Type::Integer64 => "int64".into(),
            Type::Natural8 => "nat8".into(),
            Type::Natural16 => "nat16".into(),
            Type::Natural32 => "nat32".into(),
            Type::Natural64 => "nat64".into(),
            Type::Size => "size".into(),
            Type::Offset => "offset".into(),
            Type::Float32 => "float32".into(),
            Type::Float64 => "float64".into(),
            Type::GenericInteger | Type::Generic => unreachable!(),
            Type::Null => "null".into(),
            Type::Bool => "bool".into(),
            Type::String => "string".into(),
            Type::Pointer(pointer_type, subtype) => {
                let prefix = match pointer_type {
                    PointerType::Reference => "Reference",
                    PointerType::Mutable => "Mutable",
                    PointerType::Array => "ArrayReference",
                    PointerType::ArrayMutable => "MutableArrayReference",
                };
                format!("{}To{}", prefix, self.mangle_type_name(subtype))
            },
            Type::Record(ref fields) => {
                let mut string: String = "Record".into();
                for &(ref name, type_id) in fields.iter() {
                    string.push_str(&format!("Field{}Type{}", name, self.mangle_type_name(type_id)));
                }
                string.push_str("End");
                string
            },
            Type::Function { ref argument_types, return_type } => {
                let mut output = String::new();
                output += "Function";
                for &typ in argument_types.iter() {
                    output += "Arg";
                    output += &*self.mangle_type_name(typ);
                }
                output += "Returns";
                output += &*self.mangle_type_name(return_type);
                output
            },
            Type::Array(size, subtype) => {
                format!("Array{}Of{}", size, self.mangle_type_name(subtype))
            },
            Type::Error => "error".into(),
        }
    }
}

impl<'source> Backend for LlvmBackend<'source> {
    fn initialize(&mut self) {
        for (_, &function_id) in self.compiler.signature_resolution_map.iter() {
            let function = self.compiler.get_function_info(function_id);
            let return_typeref = self.translate_type(function.return_type);
            let mut param_typerefs: Vec<LLVMTypeRef> = function.arguments.iter().map(|&x| self.translate_type(x)).collect();
            unsafe {
                let function_type = LLVMFunctionType(return_typeref, param_typerefs.as_mut_ptr(), param_typerefs.len() as _, 0);
                let name = self.mangle_function_name(function);
                let llvm_function = LLVMAddFunction(self.module, name.as_ptr(), function_type);

                self.function_map.insert(function_id, llvm_function);
            }
        }
    }

    fn translate_ir(&mut self, ir: &IrGenerator) {
        let mut function_translator = FunctionTranslator::new(self, ir);
        function_translator.translate();
    }

    fn output(&mut self, filename: &str) -> io::Result<()> {
        use std::mem::MaybeUninit;
        use std::fs;

        struct TemporaryFile(String);
        impl Drop for TemporaryFile {
            fn drop(&mut self) {
                let _ = fs::remove_file(&self.0);
            }
        }

        let s;
        let object_filename = if self.compiler.options.no_link {
            filename
        } else {
            s = TemporaryFile(format!("{}.opustmp.o", filename));
            &*s.0
        };
        let cstring = CString::new(object_filename).unwrap().into_raw();
        unsafe {
            if self.compiler.options.debug {
                LLVMDumpModule(self.module);
            }

            if LLVM_InitializeNativeTarget() != 0 {
                panic!("failed to initialize native target")
            }
            if LLVM_InitializeNativeAsmPrinter() != 0 {
                panic!("failed to initialize native asm printer")
            }
            LLVM_InitializeAllTargetMCs();
            LLVM_InitializeAllTargetInfos();

            let triple = LLVMGetDefaultTargetTriple();

            let mut target: MaybeUninit<LLVMTargetRef> = MaybeUninit::uninit();
            {
                let mut buffer: MaybeUninit<*mut _> = MaybeUninit::uninit();
                if LLVMGetTargetFromTriple(triple, target.as_mut_ptr(), buffer.as_mut_ptr()) != 0 {
                    panic!("{:?}", CString::from_raw(buffer.assume_init()))
                }
            }

            let cpu = LLVMGetHostCPUName();
            let features = LLVMGetHostCPUFeatures();
            let optimization = LLVMCodeGenOptLevel::LLVMCodeGenLevelDefault;
            let relocation = LLVMRelocMode::LLVMRelocDefault;
            let code_model = LLVMCodeModel::LLVMCodeModelDefault;
            let target_machine = LLVMCreateTargetMachine(target.assume_init(), triple, cpu, features, optimization, relocation, code_model);

            let mut buffer: MaybeUninit<*mut _> = MaybeUninit::uninit();
            if LLVMTargetMachineEmitToFile(target_machine, self.module, cstring, LLVMCodeGenFileType::LLVMObjectFile, buffer.as_mut_ptr()) != 0 {
                panic!("{:?}", CString::from_raw(buffer.assume_init()))
            }

            CString::from_raw(cstring);
        }

        // LINKING //
        if self.compiler.options.no_link {
            return Ok(())
        }

        use std::process::{Command, Stdio};
        use std::io::{Read, Write};
        let mut command = Command::new("cc");
        command.arg("-x").arg("c")
            .arg("-")
            .arg("-o").arg(filename)
            .arg("-x").arg("none")
            .arg(&*object_filename);
        for library_name in &self.compiler.options.linking {
            command.arg(format!("-l{}", library_name));
        }

        let mut compiler_process = command
            .stdin(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        let stdin = compiler_process.stdin.as_mut().expect("failed to open cc stdin");
        write!(stdin, r#"
            #include <inttypes.h>
            int32_t _opus_Main(void);
            int main(void) {{
                return _opus_Main();
            }}
        "#)?;

        let result = compiler_process.wait()?;
        let stderr = compiler_process.stderr.as_mut().expect("failed to open cc stderr");
        let mut err = String::new();
        stderr.read_to_string(&mut err).unwrap();

        if !result.success() {
            eprintln!("internal compiler error: cc exited with non-zero status");
            eprint!("{}", err);
            return Err(io::Error::from(io::ErrorKind::Other))
        }

        if err.len() != 0 {
            eprintln!("cc emitted warnings:");
            eprint!("{}", err);
        }

        Ok(())
    }
}

struct FunctionTranslator<'source> {
    backend: &'source LlvmBackend<'source>,
    ir: &'source IrGenerator<'source>,
    function: LLVMValueRef,
    bbs: Vec<LLVMBasicBlockRef>,
    bb_index: usize,
    variable_types: Vec<LLVMTypeRef>,
    variables: Vec<LLVMValueRef>,
}

impl<'source> FunctionTranslator<'source> {
    fn new(backend: &'source LlvmBackend<'source>, ir: &'source IrGenerator<'source>) -> Self {
        let function = backend.function_map[&ir.function.id];
        unsafe {
            let mut bbs = vec![];
            for _ in 0..ir.bbs.len() {
                let bb = LLVMAppendBasicBlockInContext(backend.context, function, b"\0".as_ptr() as *const _);
                bbs.push(bb);
            }

            FunctionTranslator {
                backend,
                ir,
                function,
                bbs,
                bb_index: 0,
                variable_types: vec![],
                variables: vec![LLVMConstInt(LLVMIntTypeInContext(backend.context, 32), 31337, 0); ir.variables.len()],
            }
        }
    }

    fn translate(&mut self) {
        // Load variable types
        for variable in self.ir.variables.iter() {
            self.variable_types.push(self.backend.translate_type(variable.typ));
        }

        // Load parameters
        for i in 0..self.ir.function.arguments.len() {
            unsafe {
                self.variables[i] = LLVMGetParam(self.function, i as _);
            }
        }

        for (bb_index, _) in self.ir.bbs.iter().enumerate() {
            self.translate_bb(bb_index);
        }
    }

    fn switch_to_bb(&mut self, bb_index: usize) {
        self.bb_index = bb_index;
        unsafe {
            LLVMPositionBuilderAtEnd(self.backend.builder, self.bbs[bb_index]);
        }
    }

    fn translate_bb(&mut self, bb_index: usize) {
        self.switch_to_bb(bb_index);

        let irbb = &self.ir.bbs[bb_index];
        for instruction in irbb {
            self.translate_instruction(instruction);
        }
    }

    fn translate_instruction(&mut self, instruction: &Instruction<'source>) {
        unsafe {
            match *instruction {
                Instruction::Integer(destination, constant) => {
                    let signed = self.backend.compiler.type_is_signed(self.ir.variables[destination].typ);
                    let constant = LLVMConstInt(self.variable_types[destination], constant as _, signed as _);
                    self.variables[destination] = constant;
                },
                Instruction::Float(destination, constant) => {
                    let constant = LLVMConstReal(self.variable_types[destination], constant as _);
                    self.variables[destination] = constant;
                },
                Instruction::Null(destination) => {
                    let mut vals = vec![];
                    let constant = LLVMConstStruct(vals.as_mut_ptr(), vals.len() as _, 0);
                    self.variables[destination] = constant;
                },
                Instruction::Bool(destination, is_true) => {
                    let constant = LLVMConstInt(self.variable_types[destination], is_true as _, 0);
                    self.variables[destination] = constant;
                },
                Instruction::String(destination, ref value) => {
                    let array_value = LLVMConstStringInContext(self.backend.context, (**value).as_ptr() as _, value.len() as _, 1);
                    let array_type = LLVMArrayType(LLVMInt8Type(), value.len() as _);
                    let global_value = LLVMAddGlobal(self.backend.module, array_type, b"\0".as_ptr() as *const _);
                    LLVMSetGlobalConstant(global_value, 1);
                    LLVMSetInitializer(global_value, array_value);

                    let zero = LLVMConstInt(LLVMInt32Type(), 0, 0);
                    let mut indices = vec![zero, zero];
                    let pointer = LLVMConstGEP(global_value, indices.as_mut_ptr() as _, indices.len() as _);

                    let length = LLVMConstInt(LLVMInt64TypeInContext(self.backend.context), value.len() as _, 0);
                    let mut values = vec![pointer, length];
                    self.variables[destination] = LLVMConstStruct(values.as_mut_ptr(), values.len() as _, 0);
                },

                Instruction::Sizeof(destination, type_id) => {
                    let type_ref = self.backend.translate_type(type_id);
                    self.variables[destination] = LLVMSizeOf(type_ref);
                },
                Instruction::Alignof(destination, type_id) => {
                    let type_ref = self.backend.translate_type(type_id);
                    self.variables[destination] = LLVMAlignOf(type_ref);
                },

                Instruction::Call(destination, function, ref arguments) => {
                    let llvm_function = self.variables[function];
                    let mut llvm_arguments: Vec<_> = arguments.iter().map(|&x| self.variables[x]).collect();
                    self.variables[destination] = LLVMBuildCall(self.backend.builder, llvm_function, llvm_arguments.as_mut_ptr(), llvm_arguments.len() as _, b"\0".as_ptr() as *const _);
                },

                Instruction::Allocate(destination) => {
                    let typ = self.backend.translate_type(self.ir.get_lvalue_type(destination));
                    let v = LLVMBuildAlloca(self.backend.builder, typ, b"\0".as_ptr() as *const _);
                    self.variables[destination] = v;
                },
                Instruction::Load(destination, source) => {
                    self.variables[destination] = LLVMBuildLoad(self.backend.builder, self.variables[source], b"\0".as_ptr() as *const _);
                },
                Instruction::Store(destination, source) => {
                    LLVMBuildStore(self.backend.builder, self.variables[source], self.variables[destination]);
                },
                Instruction::Field(destination, source, field_name) => {
                    // %dest = getelementptr <ty>, <ty>* source, i32 <idx>
                    let record_type = self.ir.compiler.get_type_info(self.ir.get_lvalue_type(source));
                    let index = match record_type {
                        Type::Record(ref fields) => {
                            fields.iter().position(|&(ref field_name2, _)| **field_name2 == *field_name).unwrap()
                        },
                        ref t => unreachable!("{:?}", t),
                    };

                    let mut indices = vec![LLVMConstInt(LLVMInt32Type(), 0, 0), LLVMConstInt(LLVMInt32Type(), index as _, 0)];

                    self.variables[destination] = LLVMBuildGEP(self.backend.builder, self.variables[source], indices.as_mut_ptr(), indices.len() as _, b"\0".as_ptr() as *const _);
                },
                Instruction::BuiltinField(destination, source, field_index) => {
                    let mut indices = vec![LLVMConstInt(LLVMInt32Type(), 0, 0), LLVMConstInt(LLVMInt32Type(), field_index as _, 0)];
                    self.variables[destination] = LLVMBuildGEP(self.backend.builder, self.variables[source], indices.as_mut_ptr(), indices.len() as _, b"\0".as_ptr() as *const _);
                },
                Instruction::IndexPointer(destination, source, index) => {
                    let mut indices = vec![self.variables[index]];

                    self.variables[destination] = LLVMBuildGEP(self.backend.builder, self.variables[source], indices.as_mut_ptr(), indices.len() as _, b"\0".as_ptr() as *const _);
                },
                Instruction::IndexArray(destination, source, index) => {
                    let mut indices = vec![LLVMConstInt(LLVMInt32Type(), 0, 0), self.variables[index]];

                    self.variables[destination] = LLVMBuildGEP(self.backend.builder, self.variables[source], indices.as_mut_ptr(), indices.len() as _, b"\0".as_ptr() as *const _);
                },

                Instruction::Add(destination, variable1, variable2) => {
                    if self.backend.compiler.type_is_float(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildFAdd(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else {
                        self.variables[destination] = LLVMBuildAdd(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    }
                },
                Instruction::Subtract(destination, variable1, variable2) => {
                    if self.backend.compiler.type_is_float(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildFSub(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else {
                        self.variables[destination] = LLVMBuildSub(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    }
                },
                Instruction::Multiply(destination, variable1, variable2) => {
                    if self.backend.compiler.type_is_float(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildFMul(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else {
                        self.variables[destination] = LLVMBuildMul(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    }
                },
                Instruction::Divide(destination, variable1, variable2) => {
                    if self.backend.compiler.type_is_float(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildFDiv(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else if self.ir.compiler.type_is_signed(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildSDiv(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else {
                        self.variables[destination] = LLVMBuildUDiv(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    }
                },
                Instruction::Modulo(destination, variable1, variable2) => {
                    if self.backend.compiler.type_is_float(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildFRem(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else if self.ir.compiler.type_is_signed(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildSRem(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else {
                        self.variables[destination] = LLVMBuildURem(self.backend.builder, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    }
                },
                Instruction::Equals(destination, variable1, variable2) => {
                    if self.backend.compiler.type_is_float(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildFCmp(self.backend.builder, LLVMRealPredicate::LLVMRealOEQ, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else {
                        self.variables[destination] = LLVMBuildICmp(self.backend.builder, LLVMIntPredicate::LLVMIntEQ, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    }
                },
                Instruction::LessThan(destination, variable1, variable2) => {
                    if self.backend.compiler.type_is_float(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildFCmp(self.backend.builder, LLVMRealPredicate::LLVMRealOLT, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else if self.ir.compiler.type_is_signed(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildICmp(self.backend.builder, LLVMIntPredicate::LLVMIntSLT, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else {
                        self.variables[destination] = LLVMBuildICmp(self.backend.builder, LLVMIntPredicate::LLVMIntULT, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    }
                },
                Instruction::GreaterThan(destination, variable1, variable2) => {
                    if self.backend.compiler.type_is_float(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildFCmp(self.backend.builder, LLVMRealPredicate::LLVMRealOGT, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else if self.ir.compiler.type_is_signed(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildICmp(self.backend.builder, LLVMIntPredicate::LLVMIntSGT, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else {
                        self.variables[destination] = LLVMBuildICmp(self.backend.builder, LLVMIntPredicate::LLVMIntUGT, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    }
                },
                Instruction::LessThanEquals(destination, variable1, variable2) => {
                    if self.backend.compiler.type_is_float(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildFCmp(self.backend.builder, LLVMRealPredicate::LLVMRealOLE, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else if self.ir.compiler.type_is_signed(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildICmp(self.backend.builder, LLVMIntPredicate::LLVMIntSLE, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else {
                        self.variables[destination] = LLVMBuildICmp(self.backend.builder, LLVMIntPredicate::LLVMIntULE, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    }
                },
                Instruction::GreaterThanEquals(destination, variable1, variable2) => {
                    if self.backend.compiler.type_is_float(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildFCmp(self.backend.builder, LLVMRealPredicate::LLVMRealOGE, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else if self.ir.compiler.type_is_signed(self.ir.variables[variable1].typ) {
                        self.variables[destination] = LLVMBuildICmp(self.backend.builder, LLVMIntPredicate::LLVMIntSGE, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    } else {
                        self.variables[destination] = LLVMBuildICmp(self.backend.builder, LLVMIntPredicate::LLVMIntUGE, self.variables[variable1], self.variables[variable2], b"\0".as_ptr() as *const _);
                    }
                },

                Instruction::Function(destination, function) => {
                    self.variables[destination] = self.backend.function_map[&function];
                },
                Instruction::GlobalVariable(destination, global_id) => {
                    self.variables[destination] = self.backend.global_map[&global_id];
                },
                Instruction::GlobalConstant(destination, global_id) => {
                    self.variables[destination] = self.backend.global_map[&global_id];
                },

                Instruction::Not(destination, variable) => {
                    self.variables[destination] = LLVMBuildNot(self.backend.builder, self.variables[variable], b"\0".as_ptr() as *const _);
                },
                Instruction::Negate(destination, variable) => {
                    self.variables[destination] = LLVMBuildNeg(self.backend.builder, self.variables[variable], b"\0".as_ptr() as *const _);
                },

                Instruction::Cast(cast_type, destination, source) => {
                    let destination_type = self.variable_types[destination];
                    self.variables[destination] = match cast_type {
                        CastType::None | CastType::PointerType => self.variables[source],
                        CastType::Pointer => LLVMBuildPointerCast(self.backend.builder, self.variables[source], destination_type, b"\0".as_ptr() as *const _),
                        CastType::Integer => {
                            let destination_type_id = self.ir.variables[destination].typ;
                            let source_type_id = self.ir.variables[source].typ;
                            if self.ir.compiler.int_type_width(destination_type_id) < self.ir.compiler.int_type_width(source_type_id) {
                                LLVMBuildTrunc(self.backend.builder, self.variables[source], destination_type, b"\0".as_ptr() as *const _)
                            } else if self.ir.compiler.type_is_signed(source_type_id) {
                                LLVMBuildSExt(self.backend.builder, self.variables[source], destination_type, b"\0".as_ptr() as *const _)
                            } else {
                                LLVMBuildZExt(self.backend.builder, self.variables[source], destination_type, b"\0".as_ptr() as *const _)
                            }
                        },
                        CastType::PointerToInteger => {
                            LLVMBuildPtrToInt(self.backend.builder, self.variables[source], destination_type, b"\0".as_ptr() as *const _)
                        },
                        CastType::IntegerToPointer => {
                            LLVMBuildIntToPtr(self.backend.builder, self.variables[source], destination_type, b"\0".as_ptr() as *const _)
                        },
                        CastType::PointerToArray => {
                            let mut indices = vec![LLVMConstInt(LLVMInt32Type(), 0, 0), LLVMConstInt(LLVMInt32Type(), 0, 0)];

                            LLVMBuildGEP(self.backend.builder, self.variables[source], indices.as_mut_ptr(), indices.len() as _, b"\0".as_ptr() as *const _)
                        },
                        CastType::Error => unreachable!(),
                    };
                },

                Instruction::Return(variable) => {
                    LLVMBuildRet(self.backend.builder, self.variables[variable]);
                },
                Instruction::Jump(index) => {
                    let bb = self.bbs[index];
                    LLVMBuildBr(self.backend.builder, bb);
                },
                Instruction::Branch(condition_variable, if_index, else_index) => {
                    let if_bb = self.bbs[if_index];
                    let else_bb = self.bbs[else_index];
                    LLVMBuildCondBr(self.backend.builder, self.variables[condition_variable], if_bb, else_bb);
                },
                Instruction::Unreachable => {
                    LLVMBuildUnreachable(self.backend.builder);
                },
                Instruction::Phi(destination, index1, variable1, index2, variable2) => {
                    let value = LLVMBuildPhi(self.backend.builder, self.variable_types[destination], b"\0".as_ptr() as *const _);
                    let mut values = vec![self.variables[variable1], self.variables[variable2]];
                    let mut blocks = vec![self.bbs[index1], self.bbs[index2]];
                    LLVMAddIncoming(value, values.as_mut_ptr(), blocks.as_mut_ptr(), 2);
                    self.variables[destination] = value;
                },

                Instruction::Error(..) | Instruction::BreakPlaceholder => unreachable!("{:?}", instruction),
            }
        }
    }
}
