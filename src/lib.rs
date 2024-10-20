pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Op};
use slang_ui::prelude::*;

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &mut slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;

        // Iterate methods
        for m in file.methods() {
            // Get method's preconditions;
            let pres = m.requires();
            // Merge them into a single condition
            let pre = pres
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            // Convert the expression into an SMT expression
            let spre = pre.smt()?;
            // Assert precondition
            solver.assert(spre.as_bool()?)?;

            // Get method's body
            let cmd = &m.body.clone().unwrap().cmd;
            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(cmd)?;
            // Calculate obligation and error message (if obligation is not
            // verified)
            let (oblig, msg) = wp(&ivl, &Expr::bool(true))?;
            // Convert obligation to SMT expression
            let soblig = oblig.smt()?;

            // Run the following solver-related statements in a closed scope.
            // That is, after exiting the scope, all assertions are forgotten
            // from subsequent executions of the solver
            solver.scope(|solver| {
                // Check validity of obligation
                //println!("smt_obligation {:#?} ", soblig);
                //println!("smt_obligation as bool {:#?} ", soblig.as_bool());
                solver.assert(!soblig.as_bool()?)?;
                //println!("we asserted right");
                // Run SMT solver on all current assertions
                match solver.check_sat()? {
                    // If the obligations result not valid, report the error (on
                    // the span in which the error happens)
                    smtlib::SatResult::Sat => {
                        cx.error(oblig.span, format!("{msg}"));
                    }
                    smtlib::SatResult::Unknown => {
                        cx.warning(oblig.span, "{msg}: unknown sat result");
                    }
                    smtlib::SatResult::Unsat => (),
                }
                Ok(())
            })?;
        }

        Ok(())
    }
}

// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(cmd: &Cmd) -> Result<IVLCmd> {
    //println!("cmd to ivlcmd {:#?}", &cmd.kind);
    match &cmd.kind {
        CmdKind::Assert         { condition, .. }               => Ok(IVLCmd::assert(condition, "Assert might fail!")),
        CmdKind::Seq            ( cmd1, cmd2)                   => Ok(IVLCmd::seq(&cmd_to_ivlcmd(cmd1)?, &cmd_to_ivlcmd(cmd2)?)),
        CmdKind::VarDefinition  { name, ty, expr }              => Ok(IVLCmd::vardef(name, ty, expr)),
        CmdKind::Assignment     { name, expr }                  => Ok(IVLCmd::assign(name, expr)),
        CmdKind::Assume         { condition }                   => Ok(IVLCmd::assume(condition)),
        CmdKind::Loop           { invariants, variant, body}    => Ok(IVLCmd::_loop(invariants, variant, body)),
        CmdKind::Match          { body }                        => Ok(IVLCmd::_match(body)),
        CmdKind::Return         { expr }                        => Ok(IVLCmd::_return(expr)),
        _ => todo!(" Not supported (yet)."),
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single
// assertion
fn wp(ivl: &IVLCmd, expr_in: &Expr) -> Result<(Expr, String)> {
    //println!("Finding WP of {:#?} with expr: {:#?}", &ivl.kind, &expr_in.kind);
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message }       => Ok((Expr::op(&condition.clone(), Op::And, &expr_in), message.clone())),
        IVLCmdKind::Assume { condition }                => Ok((Expr::op(&condition.clone(), Op::Imp, &expr_in), "Assume might not fail".to_string())),
        IVLCmdKind::Seq(cmd1, cmd2)                     => { if !matches!(cmd1.kind, IVLCmdKind::Return{..}) {
                                                                let (expr2, msg2) = wp(cmd2, expr_in)?;
                                                                let (expr1, msg1) = wp(cmd1, &expr2)?;
                                                                Ok((expr1,  msg2))
                                                            } else {
                                                                Ok((Expr::bool(false),  "Jeg er dum og mit return er ikke til sidst".to_string()))
                                                            }
                                                            } // should not be just msg1
                                                            //TODO: RETURN HAS TO BE LAST EXPR IF METHOD HAS RETURN

        IVLCmdKind::Assignment { name, expr }           => Ok((expr_in.clone().subst(|x| x.is_ident(&name.ident), expr), name.to_string())),//expr_in[var -> expr]
        IVLCmdKind::VarDefinition { name, expr, .. }    => {if let Some(expr) = expr {Ok((expr_in.clone().subst(|x| x.is_ident(&name.ident), expr), name.to_string()))} // has expr 
                                                            else {Ok((expr_in.clone(), "All good(not)".to_string()))}}, // doesn't have expr
        IVLCmdKind::Loop {invariants, variant, cases}    => { let mut precondition = Expr::bool(true);
                                                            for invariant in invariants.iter() {
                                                                precondition = Expr::op(&invariant.clone(), Op::And, &precondition);
                                                            };
                                                            Ok((precondition.clone(), "Something wrong with the Loop yo".to_string()))// i && expr_in
                                                            },
        IVLCmdKind::Match { body } => { let mut precondition = Expr::bool(true);
                                        let mut _message ="No cases found".to_string();
                                        for case in body.cases.iter() {
                                            let (wp_case, msg_case) = wp(&cmd_to_ivlcmd(&case.cmd)?, expr_in)?;

                                            let implication = Expr::op(&case.condition, Op::Imp, &wp_case);
                                            
                                            precondition = Expr::op(&implication.clone(), Op::And, &precondition);
                                            _message = msg_case; //Always gets last error message
                                        }
                                        Ok((precondition.clone(), _message))
                                        },
        IVLCmdKind::Return { expr }      => { let mut _message  = "".to_string();
                                            if let Some(expr) = expr {_message = ["Failed in returning expression:", (&expr.to_string())].join(" ")} 
                                            else {_message = "Failed returning".to_string();}
                                            Ok((expr_in.clone(), _message.to_string()))
                                            }, 
        
        _ => todo!("Not supported (yet)."),
    }
}
