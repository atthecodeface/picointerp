//a TL Operations
//it TLBinOp
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TLBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Xor,
    Lsl,
    Lsr,
    Asr,
}

//ip Display for TLBinOp
impl std::fmt::Display for TLBinOp {
    //mp fmt - format for display
    /// Display in human-readble form
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "Add"),
            Self::Sub => write!(f, "Sub"),
            Self::Mul => write!(f, "Mul"),
            Self::Div => write!(f, "Div"),
            Self::Mod => write!(f, "Mod"),
            Self::And => write!(f, "And"),
            Self::Or  => write!(f, "Or"),
            Self::Xor => write!(f, "Xor"),
            Self::Lsl => write!(f, "Lsl"),
            Self::Lsr => write!(f, "Lsr"),
            Self::Asr => write!(f, "Asr"),
        }

    }
}
//it TLUnOp
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TLUnOp {
    BoolNot,
    Neg
}

//ip Display for TLUOp
impl std::fmt::Display for TLUnOp {
    //mp fmt - format for display
    /// Display in human-readble form
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::BoolNot => write!(f, "BoolNot"),
            Self::Neg => write!(f, "Neg"),
        }
    }
}

//it TLCmpOp
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TLCmpOp {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    Ult,
    Uge,
}

//ip Display for TLCmpOp
impl std::fmt::Display for TLCmpOp {
    //mp fmt - format for display
    /// Display in human-readble form
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Eq => write!(f, "Eq"),
            Self::Ne => write!(f, "Ne"),
            Self::Lt => write!(f, "Lt"),
            Self::Gt => write!(f, "Gt"),
            Self::Le => write!(f, "Le"),
            Self::Ge => write!(f, "Ge"),
            Self::Ult => write!(f, "Ult"),
            Self::Uge => write!(f, "Uge"),
        }
    }
}

