use slang::{
    ast::{Expr, Name, Type, Cases},
    Span,
};
use slang_ui::prelude::*;

use crate::ivl::{IVLCmd, IVLCmdKind};

impl IVLCmd {
    pub fn new(kind: IVLCmdKind) -> IVLCmd {
        IVLCmd {
            span: kind.infer_span().unwrap_or_default(),
            kind,
        }
    }
    pub fn vardef(name: &Name, ty: &(Span, Type), expr: &Option<Expr>) -> IVLCmd {
        IVLCmd::new(IVLCmdKind::VarDefinition {
            name: name.clone(),
            ty: (Span::default(), ty.1.clone()),
            expr: expr.clone(),
        })
    }
    pub fn assign(name: &Name, expr: &Expr) -> IVLCmd {
        IVLCmd {
            span: Span::default(),
            kind: IVLCmdKind::Assignment {
                name: name.clone(),
                expr: expr.clone(),
            },
        }
    }
    pub fn seq(&self, other: &IVLCmd) -> IVLCmd {
        IVLCmd {
            span: Span::default(),
            kind: IVLCmdKind::Seq(Box::new(self.clone()), Box::new(other.clone())),
        }
    }
    pub fn _loop(invariants: &Vec<Expr>, variant: &Option<Expr>, cases: &Cases) -> IVLCmd {
        IVLCmd {
            span: Span::default(),
            kind: IVLCmdKind::Loop {
                invariants: invariants.to_vec(),
                variant: variant.clone(), 
                cases: cases.clone(),
            }
        }
    }
    pub fn _match(body: &Cases) -> IVLCmd {
        IVLCmd {
            span: Span::default(),
            kind: IVLCmdKind::Match {
                body: body.clone(),
            }
        }
    }
    pub fn seqs(cmds: &[IVLCmd]) -> IVLCmd {
        cmds.iter()
            .cloned()
            .reduce(|a, b| IVLCmd::seq(&a, &b))
            .unwrap_or(IVLCmd::nop())
    }
    pub fn _return(expr: &Option<Expr>) -> IVLCmd {
        IVLCmd {
            span: Span::default(),
            kind: IVLCmdKind::Return {
                expr: expr.clone(),
            }
        }
    }
    pub fn nondet(&self, other: &IVLCmd) -> IVLCmd {
        IVLCmd {
            span: Span::default(),
            kind: IVLCmdKind::NonDet(Box::new(self.clone()), Box::new(other.clone())),
        }
    }
    pub fn nondets(cmds: &[IVLCmd]) -> IVLCmd {
        cmds.iter()
            .cloned()
            .reduce(|a, b| IVLCmd::nondet(&a, &b))
            .unwrap_or(IVLCmd::unreachable())
    }
    pub fn assume(condition: &Expr) -> IVLCmd {
        IVLCmd {
            span: Span::default(),
            kind: IVLCmdKind::Assume {
                condition: condition.clone(),
            },
        }
    }
    pub fn assert(condition: &Expr, message: &str) -> IVLCmd {
        IVLCmd {
            span: Span::default(),
            kind: IVLCmdKind::Assert {
                condition: condition.clone(),
                message: message.to_owned(),
            },
        }
    }
    pub fn havoc(name: &Name, ty: &Type) -> IVLCmd {
        IVLCmd {
            kind: IVLCmdKind::Havoc {
                name: name.clone(),
                ty: ty.clone(),
            },
            span: Span::default(),
        }
    }
    pub fn nop() -> IVLCmd {
        IVLCmd::assume(&Expr::bool(true))
    }
    pub fn unreachable() -> IVLCmd {
        IVLCmd::assume(&Expr::bool(false))
    }
}
impl IVLCmdKind {
    fn infer_span(&self) -> Option<Span> {
        Some(match self {
            IVLCmdKind::VarDefinition { name, ty, expr } => {
                let type_span = ty.0;
                if let Some(expr) = expr {
                    name.span.union(type_span).union(expr.span)
                } else {
                    name.span.union(type_span)
                }
            }
            _ => todo!("Not supported (yet)."),
        }
    )
    }
}

impl std::fmt::Display for IVLCmd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            IVLCmdKind::VarDefinition { name, ty, expr } => {if let Some(expr) = expr {write!(f, "Var {name} : {0} := {expr}", ty.1)} 
                                                            else {write!(f, "Var {name} : {0}", ty.1)}},
            IVLCmdKind::Assignment { name, expr } => write!(f, "{name} := {expr}"),
            IVLCmdKind::Havoc { name, .. } => write!(f, "havoc {name}"),
            IVLCmdKind::Assume { condition } => write!(f, "assume {condition}"),
            IVLCmdKind::Assert { condition, .. } => write!(f, "assert {condition}"),
            //ENSURES
            //REQUIRES
            IVLCmdKind::Seq(c1, c2) => write!(f, "{c1} ; {c2}"),
            IVLCmdKind::NonDet(c1, c2) => write!(f, "{{ {c1} }} [] {{ {c2} }}"),
            IVLCmdKind::Loop {invariants, variant, cases} => write!(f, "loop {{ }}"),
            IVLCmdKind::Match {body} => write!(f, "match {{ }}"),
            IVLCmdKind::Return {expr} => {if let Some(expr) = expr {write!(f, "return {expr}")} else {write!(f, "returned nothing")}}
        }
    }
}
