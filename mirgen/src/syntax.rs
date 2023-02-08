use crate::vec::{Idx, IndexVec};

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

declare_id!(BasicBlock);
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
}

impl BasicBlock {
    pub fn identifier(&self) -> String {
        format!("bb{}", self.index())
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

impl Local {
    pub fn identifier(&self) -> String {
        if self.index() == 0 {
            "RET".to_owned()
        } else {
            format!("_{}", self.index())
        }
    }
}
pub struct Body {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData>,
    pub locals: IndexVec<Local, LocalDecl>,
}

pub struct Place {
    pub local: Local,
    // TODO: mir_field and mir_variant
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
    // define!("mir_call", fn Call<T>(place: T, goto: BasicBlock, call: T));
    Call {
        destination: Place,
        target: BasicBlock,
        // TODO: this probably isn't a place
        func: Place,
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
    branches: Vec<(u128, BasicBlock)>,
    otherwise: BasicBlock,
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

pub enum Rvalue {
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

pub enum Operand {
    Copy(Place),
    // define!("mir_move", fn Move<T>(place: T) -> T);
    Move(Place),
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

pub enum Mutability {
    // N.B. Order is deliberate, so that Not < Mut
    Not,
    Mut,
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

enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

pub enum FloatTy {
    F32,
    F64,
}

pub enum Ty {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
}

impl Ty {
    pub fn name(&self) -> &'static str {
        match self {
            Ty::Bool => "bool",
            Ty::Char => "char",
            Ty::Int(size) => match size {
                IntTy::Isize => "isize",
                IntTy::I8 => "i8",
                IntTy::I16 => "i16",
                IntTy::I32 => "i32",
                IntTy::I64 => "i64",
                IntTy::I128 => "i128",
            },
            Ty::Uint(size) => match size {
                UintTy::Usize => "usize",
                UintTy::U8 => "u8",
                UintTy::U16 => "u16",
                UintTy::U32 => "u32",
                UintTy::U64 => "u64",
                UintTy::U128 => "u128",
            },
            Ty::Float(size) => match size {
                FloatTy::F32 => "f32",
                FloatTy::F64 => "f64",
            },
        }
    }
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
