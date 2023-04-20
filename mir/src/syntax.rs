use std::num::TryFromIntError;

use index_vec::{define_index_type, IndexVec};

use crate::serialize::Serialize;

pub struct Program {
    pub functions: IndexVec<Function, Body>,
    pub entry_args: Vec<Literal>,
}

pub type LocalDecls = IndexVec<Local, LocalDecl>;

define_index_type! {pub struct Function = u32;}
pub struct Body {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData>,
    pub local_decls: LocalDecls,
    arg_count: usize,
}

define_index_type! {pub struct BasicBlock = u32;}
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

impl BasicBlockData {
    /// An empty basic block
    pub fn new() -> Self {
        Self {
            statements: vec![],
            terminator: Terminator::Hole,
        }
    }

    pub fn insert_statement(&mut self, stmt: Statement) {
        self.statements.push(stmt);
    }
}

define_index_type! {pub struct Local = u32;}
pub struct LocalDecl {
    /// Whether this is a mutable binding (i.e., `let x` or `let mut x`).
    ///
    /// Temporaries and the return place are always mutable.
    pub mutability: Mutability,

    /// If this local is a temporary and `is_block_tail` is `Some`,
    /// The type of this local.
    pub ty: Ty,
}

define_index_type! {pub struct FieldIdx = u32;}
define_index_type! {pub struct VariantIdx = u32;}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Place {
    Hole,
    Place {
        local: Local,
        projection: Vec<ProjectionElem>,
    },
}
impl Place {
    pub const fn from_local(local: Local) -> Self {
        Place::Place {
            local,
            projection: vec![],
        }
    }

    pub fn from_projected(local: Local, projections: &[ProjectionElem]) -> Self {
        Place::Place {
            local,
            projection: Vec::from(projections),
        }
    }

    pub fn local(&self) -> Local {
        match self {
            Place::Place { local, .. } => *local,
            Place::Hole => panic!("place is a hole"),
        }
    }

    pub fn projection(&self) -> &[ProjectionElem] {
        match self {
            Place::Place { projection, .. } => projection,
            Place::Hole => panic!("place is a hole"),
        }
    }

    pub fn project(&self, proj: ProjectionElem) -> Self {
        // TODO: validation
        match self.clone() {
            Place::Place {
                local,
                mut projection,
            } => {
                projection.push(proj);
                Place::Place { local, projection }
            }
            Place::Hole => panic!("place is a hole"),
        }
    }

    pub fn ty(&self, local_decl: &LocalDecls) -> Ty {
        local_decl[self.local()].ty.projected_ty(self.projection())
    }
}

impl From<Local> for Place {
    fn from(value: Local) -> Self {
        Self::from_local(value)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProjectionElem {
    Deref,
    /// This should be the same as Field, but to allow for context free serialization
    /// we separate it out
    TupleField(FieldIdx),
    Field(FieldIdx),
    Index(Local),
    Downcast(VariantIdx),
    ConstantIndex {
        offset: u64,
    },
    // TODO: Subslice
}

pub enum Terminator {
    Hole,
    // define!("mir_return", fn Return() -> BasicBlock);
    Return,
    // define!("mir_goto", fn Goto(destination: BasicBlock) -> BasicBlock);
    Goto {
        target: BasicBlock,
    },
    // define!("mir_unreachable", fn Unreachable() -> BasicBlock);
    Unreachable,
    // define!("mir_drop", fn Drop<T>(place: T, goto: BasicBlock));
    Drop {
        place: Place,
        target: BasicBlock,
    },
    // TODO: define!("mir_call", fn Call<T>(place: T, goto: BasicBlock, call: T));
    Call {
        func: Function,
        destination: Place,
        target: BasicBlock,
        args: Vec<Operand>,
    },
    /// Switches based on the computed value.
    ///
    /// First, evaluates the `discr` operand. The type of the operand must be a signed or unsigned
    /// integer, char, or bool, and must match the given type. Then, if the list of switch targets
    /// contains the computed value, continues execution at the associated basic block. Otherwise,
    /// continues execution at the "otherwise" basic block.
    ///
    /// Target values may not appear more than once.
    SwitchInt {
        /// The discriminant value being tested.
        discr: Operand,
        targets: SwitchTargets,
    },
}

pub struct SwitchTargets {
    pub branches: Vec<(u128, BasicBlock)>,
    pub otherwise: BasicBlock,
}

pub enum Rvalue {
    Use(Operand),
    UnaryOp(UnOp, Operand),
    BinaryOp(BinOp, Operand, Operand),
    Cast(Operand, Ty),
    // define!("mir_checked", fn Checked<T>(binop: T) -> (T, bool));
    CheckedBinaryOp(BinOp, Operand, Operand),
    // define!("mir_len", fn Len<T>(place: T) -> usize);
    Len(Place),
    // define!("mir_discriminant",fn Discriminant<T>(place: T) -> <T as ::core::marker::DiscriminantKind>::Discriminant);
    Discriminant(Place),
    AddressOf(Mutability, Place),
}

#[derive(Debug, Clone)]
pub enum Literal {
    Uint(u128, UintTy),
    Int(i128, IntTy),
    Bool(bool),
    Char(char),
    Tuple(Vec<Literal>),
    // Every f32 can be expressed exactly as f64
    Float(f64, FloatTy),
}

pub enum Operand {
    Copy(Place),
    // define!("mir_move", fn Move<T>(place: T) -> T);
    Move(Place),
    Constant(Literal),
    // TODO: the following
    // define!("mir_static", fn Static<T>(s: T) -> &'static T);
    // define!("mir_static_mut", fn StaticMut<T>(s: T) -> *mut T);
}

impl Operand {
    pub fn ty(&self, local_decls: &LocalDecls) -> Ty {
        match self {
            Operand::Copy(place) | Operand::Move(place) => place.ty(local_decls),
            Operand::Constant(lit) => lit.ty(),
        }
    }
}

pub enum Statement {
    Assign(Place, Rvalue),
    // define!("mir_storage_live", fn StorageLive<T>(local: T));
    StorageLive(Local),
    // define!("mir_storage_dead", fn StorageDead<T>(local: T));
    StorageDead(Local),
    // define!("mir_storage_live", fn StorageLive<T>(local: T));
    Deinit(Place),
    // define!("mir_set_discriminant", fn SetDiscriminant<T>(place: T, index: u32));
    SetDiscriminant(Place, u32),
    // define!("mir_retag", fn Retag<T>(place: T));
    Retag(Place),
    Nop,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Mutability {
    // N.B. Order is deliberate, so that Not < Mut
    Not,
    Mut,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FloatTy {
    F32,
    F64,
}

define_index_type! {pub struct TyId = u32;}
#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub enum Ty {
    // Scalars
    Unit,
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    // Composite
    RawPtr(Box<Ty>, Mutability),
    Tuple(Vec<Ty>),
    // User-defined
    Adt(Adt),
    // TODO: more types
}

impl Ty {
    pub const BOOL: Self = Ty::Bool;
    pub const CHAR: Self = Ty::Char;
    pub const ISIZE: Self = Ty::Int(IntTy::Isize);
    pub const I8: Self = Ty::Int(IntTy::I8);
    pub const I16: Self = Ty::Int(IntTy::I16);
    pub const I32: Self = Ty::Int(IntTy::I32);
    pub const I64: Self = Ty::Int(IntTy::I64);
    pub const I128: Self = Ty::Int(IntTy::I128);
    pub const USIZE: Self = Ty::Uint(UintTy::Usize);
    pub const U8: Self = Ty::Uint(UintTy::U8);
    pub const U16: Self = Ty::Uint(UintTy::U16);
    pub const U32: Self = Ty::Uint(UintTy::U32);
    pub const U64: Self = Ty::Uint(UintTy::U64);
    pub const U128: Self = Ty::Uint(UintTy::U128);
    pub const F32: Self = Ty::Float(FloatTy::F32);
    pub const F64: Self = Ty::Float(FloatTy::F64);

    pub const INTS: [Self; 6] = [
        Self::ISIZE,
        Self::I8,
        Self::I16,
        Self::I32,
        Self::I64,
        Self::I128,
    ];

    pub const UINTS: [Self; 6] = [
        Self::USIZE,
        Self::U8,
        Self::U16,
        Self::U32,
        Self::U64,
        Self::U128,
    ];

    pub const FLOATS: [Self; 2] = [Self::F32, Self::F64];

    pub fn tuple_elems(&self) -> Option<&[Ty]> {
        match self {
            Ty::Tuple(tys) => Some(tys),
            _ => None,
        }
    }

    pub fn is_checked_binary_op_lhs(&self) -> bool {
        match self {
            Ty::Tuple(elems) => matches!(
                elems.as_slice(),
                &[Ty::Int(..) | Ty::Float(..) | Ty::Uint(..), Ty::Bool]
            ),
            _ => false,
        }
    }

    // TODO: are pointers scalar?
    pub fn is_scalar(&self) -> bool {
        match *self {
            Self::ISIZE
            | Self::I8
            | Self::I16
            | Self::I32
            | Self::I64
            | Self::I128
            | Self::USIZE
            | Self::U8
            | Self::U16
            | Self::U32
            | Self::U64
            | Self::U128
            | Self::F32
            | Self::F64
            | Self::Bool
            | Self::Char
            | Self::Unit => true,
            _ => false,
        }
    }

    pub fn projected_ty(&self, projs: &[ProjectionElem]) -> Self {
        match projs {
            [] => self.clone(),
            [head, tail @ ..] => {
                let projected = match head {
                    ProjectionElem::Deref => match self {
                        Ty::RawPtr(pointee, ..) => *pointee.clone(),
                        _ => panic!("not a reference"),
                    },
                    ProjectionElem::TupleField(idx) => {
                        self.tuple_elems().expect("is a tuple")[idx.index()].clone()
                    }
                    ProjectionElem::Downcast(_) => self.clone(),
                    ProjectionElem::Index(_) => todo!(),
                    ProjectionElem::ConstantIndex { .. } => todo!(),
                    ProjectionElem::Field(_) => todo!(),
                };
                projected.projected_ty(tail)
            }
        }
    }

    pub fn contains<P>(&self, mut predicate: P) -> bool
    where
        P: FnMut(&Ty) -> bool,
    {
        if predicate(self) {
            return true;
        }
        match self {
            Ty::Tuple(elems) => elems.iter().any(predicate),
            Ty::Adt(_) => todo!(),
            _ => false,
        }
    }

    // pub fn is_ref(self) -> bool {
    //     matches!(self, Ty::Ref(..))
    // }

    pub fn is_unsafe_ptr(&self) -> bool {
        matches!(self, Ty::RawPtr(..))
    }

    pub fn is_any_ptr(&self) -> bool {
        self.is_unsafe_ptr()
    }

    pub fn pointee_ty(&self) -> Option<Self> {
        match self {
            Ty::RawPtr(box ty, ..) => Some(ty.clone()),
            _ => None
        }
    }
}

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub struct VariantDef {
    // TODO: finish this
}

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub struct Adt {
    variants: IndexVec<VariantIdx, VariantDef>,
}

#[derive(Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    Offset,
}

#[derive(Clone, Copy)]
pub enum UnOp {
    Hole,
    Not,
    Neg,
}

impl Literal {
    pub fn ty(&self) -> Ty {
        match self {
            Literal::Int(_, ty) => Ty::Int(*ty),
            Literal::Uint(_, ty) => Ty::Uint(*ty),
            Literal::Bool(_) => Ty::Bool,
            Literal::Char(_) => Ty::Char,
            Literal::Tuple(elems) => Ty::Tuple(elems.iter().map(|lit| lit.ty()).collect()),
            Literal::Float(_, ty) => Ty::Float(*ty),
        }
    }
}

impl From<bool> for Literal {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl From<char> for Literal {
    fn from(value: char) -> Self {
        Self::Char(value)
    }
}

impl From<u8> for Literal {
    fn from(value: u8) -> Self {
        Self::Uint(value as u128, UintTy::U8)
    }
}
impl From<u16> for Literal {
    fn from(value: u16) -> Self {
        Self::Uint(value as u128, UintTy::U16)
    }
}
impl From<u32> for Literal {
    fn from(value: u32) -> Self {
        Self::Uint(value as u128, UintTy::U32)
    }
}
impl From<u64> for Literal {
    fn from(value: u64) -> Self {
        Self::Uint(value as u128, UintTy::U64)
    }
}
impl From<u128> for Literal {
    fn from(value: u128) -> Self {
        Self::Uint(value, UintTy::U128)
    }
}
impl TryFrom<usize> for Literal {
    type Error = TryFromIntError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        Ok(Self::Uint(value.try_into()?, UintTy::Usize))
    }
}
impl From<i8> for Literal {
    fn from(value: i8) -> Self {
        Self::Int(value as i128, IntTy::I8)
    }
}
impl From<i16> for Literal {
    fn from(value: i16) -> Self {
        Self::Int(value as i128, IntTy::I16)
    }
}
impl From<i32> for Literal {
    fn from(value: i32) -> Self {
        Self::Int(value as i128, IntTy::I32)
    }
}
impl From<i64> for Literal {
    fn from(value: i64) -> Self {
        Self::Int(value as i128, IntTy::I64)
    }
}
impl From<i128> for Literal {
    fn from(value: i128) -> Self {
        Self::Int(value, IntTy::I128)
    }
}
impl TryFrom<isize> for Literal {
    type Error = TryFromIntError;

    fn try_from(value: isize) -> Result<Self, Self::Error> {
        Ok(Self::Int(value.try_into()?, IntTy::Isize))
    }
}

impl From<f32> for Literal {
    fn from(value: f32) -> Self {
        Self::Float(value as f64, FloatTy::F32)
    }
}

impl From<f64> for Literal {
    fn from(value: f64) -> Self {
        Self::Float(value, FloatTy::F64)
    }
}

impl Program {
    pub const FUNCTION_ATTRIBUTE: &str =
        "#[custom_mir(dialect = \"runtime\", phase = \"optimized\")]";
    pub const HEADER: &str = "#![recursion_limit = \"256\"]
    #![feature(custom_mir, core_intrinsics)]
    #![allow(unused_parens, unused_assignments, overflowing_literals)]
    extern crate core;
    use core::intrinsics::mir::*;\n";

    // A new, empty function
    pub fn new() -> Self {
        Self {
            functions: IndexVec::default(),
            entry_args: vec![],
        }
    }

    pub fn push_fn(&mut self, body: Body) -> Function {
        self.functions.push(body)
    }

    pub fn set_entry_args(&mut self, args: &[Literal]) {
        self.entry_args = Vec::from(args);
    }
}

impl Function {
    pub fn identifier(&self) -> String {
        format!("fn{}", self.index())
    }
}

impl SwitchTargets {
    pub fn match_arms(&self) -> String {
        let mut arms: String = self
            .branches
            .iter()
            .map(|(val, bb)| format!("{val} => {},\n", bb.identifier()))
            .collect();
        arms.push_str(&format!("_ => {}", self.otherwise.identifier()));
        arms
    }
}

impl LocalDecl {
    pub fn new_mut(ty: Ty) -> Self {
        Self {
            mutability: Mutability::Mut,
            ty,
        }
    }
}

impl Local {
    pub const RET: Self = Self::from_raw_unchecked(0);
    pub fn identifier(&self) -> String {
        if *self == Self::RET {
            "RET".to_owned()
        } else {
            format!("_{}", self.index())
        }
    }
}

impl Body {
    pub fn new(args: &[Ty], return_ty: Ty) -> Self {
        let mut locals = IndexVec::new();
        locals.push(LocalDecl::new_mut(return_ty));
        // TODO: args shouldn't always be mut
        args.iter().for_each(|ty| {
            locals.push(LocalDecl::new_mut(ty.clone()));
        });
        Self {
            basic_blocks: IndexVec::new(),
            local_decls: locals,

            arg_count: args.len(),
        }
    }

    pub fn args_list(&self) -> String {
        self.args_iter()
            .map(|arg| {
                let decl = &self.local_decls[arg];
                format!(
                    "{}{}: {}",
                    decl.mutability.prefix_str(),
                    arg.identifier(),
                    decl.ty.serialize()
                )
            })
            .intersperse(",".to_string())
            .collect()
    }

    pub fn is_arg(&self, local: Local) -> bool {
        (1..self.arg_count).contains(&local.index())
    }

    /// Returns an iterator over function arguments
    pub fn args_iter(&self) -> impl Iterator<Item = Local> + ExactSizeIterator {
        (1..self.arg_count + 1).map(Local::new)
    }

    pub fn args_decl_iter(&self) -> impl Iterator<Item = (Local, &LocalDecl)> + ExactSizeIterator {
        self.args_iter()
            .map(|local| (local, &self.local_decls[local]))
    }

    /// Returns an iterator over locals defined in the function body
    pub fn vars_iter(&self) -> impl Iterator<Item = Local> + ExactSizeIterator {
        (self.arg_count + 1..self.local_decls.len()).map(Local::new)
    }

    pub fn vars_decl_iter(&self) -> impl Iterator<Item = (Local, &LocalDecl)> + ExactSizeIterator {
        self.vars_iter()
            .map(|local| (local, &self.local_decls[local]))
    }

    pub fn return_ty(&self) -> Ty {
        self.local_decls[Local::RET].ty.clone()
    }

    pub fn declare_new_var(&mut self, mutability: Mutability, ty: Ty) -> Local {
        self.local_decls.push(LocalDecl { mutability, ty })
    }

    pub fn new_basic_block(&mut self, bb: BasicBlockData) -> BasicBlock {
        self.basic_blocks.push(bb)
    }
}

impl BasicBlock {
    pub fn identifier(&self) -> String {
        format!("bb{}", self.index())
    }
}

impl Mutability {
    /// Returns `""` (empty string) or `"mut "` depending on the mutability.
    pub fn prefix_str(&self) -> &'static str {
        match self {
            Mutability::Mut => "mut ",
            Mutability::Not => "",
        }
    }

    pub fn ptr_prefix_str(&self) -> &'static str {
        match self {
            Mutability::Mut => "*mut ",
            Mutability::Not => "*const ",
        }
    }
}

impl Place {
    pub const RETURN_SLOT: Self = Self::from_local(Local::RET);
}

impl BinOp {
    pub fn symbol(&self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::BitXor => "^",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::Eq => "==",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Ne => "!=",
            BinOp::Ge => ">=",
            BinOp::Gt => ">",
            BinOp::Offset => panic!("offset is not a real infix operator"),
        }
    }
}

impl UnOp {
    pub fn symbol(&self) -> &'static str {
        match self {
            UnOp::Not => "!",
            UnOp::Neg => "-",
            UnOp::Hole => panic!("op is a hole"),
        }
    }
}
