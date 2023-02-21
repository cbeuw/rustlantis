use crate::{
    serialize::Serialize,
    vec::{Idx, IndexVec},
};

macro_rules! declare_id {
    ($name: ident) => {
        #[derive(Clone, Copy, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
        pub struct $name(u32);

        impl Idx for $name {
            fn new(idx: usize) -> Self {
                $name(idx.try_into().unwrap())
            }
            fn index(self) -> usize {
                // See the comment in `Self::new`.
                // (This cannot underflow because self is NonZeroU32.)
                usize::try_from(self.0).unwrap()
            }
        }
    };
}

declare_id!(Ty);
pub struct Program {
    pub functions: IndexVec<Function, Body>,
    pub tys: IndexVec<Ty, TyData>,
}

impl Ty {
    // Primitives
    pub const BOOL: Self = Self(0);
    pub const CHAR: Self = Self(1);
    pub const ISIZE: Self = Self(2);
    pub const I8: Self = Self(3);
    pub const I16: Self = Self(4);
    pub const I32: Self = Self(5);
    pub const I64: Self = Self(6);
    pub const I128: Self = Self(7);
    pub const USIZE: Self = Self(8);
    pub const U8: Self = Self(9);
    pub const U16: Self = Self(10);
    pub const U32: Self = Self(11);
    pub const U64: Self = Self(12);
    pub const U128: Self = Self(13);
    pub const F32: Self = Self(14);
    pub const F64: Self = Self(15);
}

declare_id!(Function);
pub struct Body {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData>,
    pub local_decls: IndexVec<Local, LocalDecl>,

    arg_count: usize,
}

declare_id!(BasicBlock);
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
}

impl BasicBlockData {
    pub fn insert_statement(&mut self, stmt: Statement) {
        self.statements.push(stmt);
    }
}

declare_id!(Local);
pub struct LocalDecl {
    /// Whether this is a mutable binding (i.e., `let x` or `let mut x`).
    ///
    /// Temporaries and the return place are always mutable.
    pub mutability: Mutability,

    /// If this local is a temporary and `is_block_tail` is `Some`,
    /// The type of this local.
    pub ty: Ty,
}

pub struct FieldIdx(u32);
declare_id!(VariantIdx);

pub struct Place {
    pub local: Local,
    pub projection: Vec<ProjectionElem>,
    // TODO: mir_field and mir_variant
}

impl Place {
    pub const fn from_local(local: Local) -> Self {
        Place {
            local,
            projection: vec![],
        }
    }
}

pub enum ProjectionElem {
    Deref,
    Field(FieldIdx),
    Index(Local),
    Downcast(VariantIdx),
    // TODO: ConstantIndex, Subslice
}

pub enum Terminator {
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
    // define!("mir_drop_and_replace", fn DropAndReplace<T>(place: T, value: T, goto: BasicBlock));
    DropAndReplace {
        place: Place,
        value: Operand,
        target: BasicBlock,
    },
    // TODO: define!("mir_call", fn Call<T>(place: T, goto: BasicBlock, call: T));
    // Call {
    //     destination: Place,
    //     target: BasicBlock,
    //     // TODO: this probably isn't a place
    //     func: Place,
    //     args: Vec<Operand>,
    // },
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
    branches: Vec<(u128, BasicBlock)>,
    otherwise: BasicBlock,
}

pub enum Rvalue {
    Hole,
    Use(Operand),
    UnaryOp(UnOp, Operand),
    BinaryOp(BinOp, Operand, Operand),
    // define!("mir_checked", fn Checked<T>(binop: T) -> (T, bool));
    CheckedBinaryOp(BinOp, Operand, Operand),
    // define!("mir_len", fn Len<T>(place: T) -> usize);
    Len(Place),
    // define!("mir_retag", fn Retag<T>(place: T));
    Retag(Place),
    // define!("mir_discriminant",fn Discriminant<T>(place: T) -> <T as ::core::marker::DiscriminantKind>::Discriminant);
    Discriminant(Place),
}

pub enum Constant {
    Int(u128),
    Bool(bool),
}

pub enum Operand {
    Hole,
    Copy(Place),
    // define!("mir_move", fn Move<T>(place: T) -> T);
    Move(Place),
    Constant(Constant, Ty),
    // TODO: the following
    // define!("mir_static", fn Static<T>(s: T) -> &'static T);
    // define!("mir_static_mut", fn StaticMut<T>(s: T) -> *mut T);
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
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mutability {
    // N.B. Order is deliberate, so that Not < Mut
    Not,
    Mut,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FloatTy {
    F32,
    F64,
}

#[derive(PartialEq, Eq)]
pub enum TyData {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Adt(Adt),
    // TODO: more types
}

#[derive(PartialEq, Eq)]
pub struct VariantDef {
    // TODO: finish this
}

#[derive(PartialEq, Eq)]
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
    Not,
    Neg,
}

impl Program {
    // TODO: match fn0's param
    pub const MAIN: &str = "pub fn main(){fn0(true);}";
    pub const FUNCTION_ATTRIBUTE: &str =
        "#[custom_mir(dialect = \"runtime\", phase = \"optimized\")]";
    pub const HEADER: &str = "#![feature(custom_mir, core_intrinsics)]\nextern crate core;\nuse core::intrinsics::mir::*;\n";

    pub fn new() -> Self {
        // Important: the order here must match the const definitions in Ty
        let tys = IndexVec::from_iter([
            TyData::Bool,
            TyData::Char,
            TyData::Int(IntTy::Isize),
            TyData::Int(IntTy::I8),
            TyData::Int(IntTy::I16),
            TyData::Int(IntTy::I32),
            TyData::Int(IntTy::I64),
            TyData::Int(IntTy::I128),
            TyData::Uint(UintTy::Usize),
            TyData::Uint(UintTy::U8),
            TyData::Uint(UintTy::U16),
            TyData::Uint(UintTy::U32),
            TyData::Uint(UintTy::U64),
            TyData::Uint(UintTy::U128),
            TyData::Float(FloatTy::F32),
            TyData::Float(FloatTy::F64),
        ]);
        Self {
            functions: IndexVec::default(),
            tys,
        }
    }

    pub fn push_fn(&mut self, body: Body) -> Function {
        self.functions.push(body)
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
    pub const RET: Self = Self(0);
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
            locals.push(LocalDecl::new_mut(*ty));
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

    pub fn vars_and_args_iter(&self) -> impl Iterator<Item = Local> + ExactSizeIterator {
        (1..self.local_decls.len()).map(Local::new)
    }

    pub fn vars_and_args_decl_iter(
        &self,
    ) -> impl Iterator<Item = (Local, &LocalDecl)> + ExactSizeIterator {
        self.vars_and_args_iter()
            .map(|local| (local, &self.local_decls[local]))
    }

    /// Returns an iterator over function arguments
    pub fn args_iter(&self) -> impl Iterator<Item = Local> + ExactSizeIterator {
        (1..self.arg_count + 1).map(Local::new)
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
        self.local_decls[Local::RET].ty
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
        }
    }
}
