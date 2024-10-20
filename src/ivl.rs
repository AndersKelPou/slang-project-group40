use slang::{
    ast::{Expr, Name, Type, Cases},
    Span,
};
use slang_ui::prelude::*;

#[derive(Debug, Clone)]
pub struct IVLCmd {
    pub span: Span,
    pub kind: IVLCmdKind,
}

#[derive(Debug, Clone)]
pub enum IVLCmdKind {
    VarDefinition {name: Name, ty: (Span, Type), expr: Option<Expr>},
    Assignment { name: Name, expr: Expr },
    Havoc { name: Name, ty: Type },

    Assume { condition: Expr },
    Assert { condition: Expr, message: String },

    Match { body: Cases },
    Loop { invariants: Vec<Expr>, variant: Option<Expr>, cases: Cases},

    Return { expr: Option<Expr> },

    Seq(Box<IVLCmd>, Box<IVLCmd>),
    NonDet(Box<IVLCmd>, Box<IVLCmd>),
}
