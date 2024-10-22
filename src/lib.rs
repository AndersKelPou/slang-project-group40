#![allow(unused)]

pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Op, ExprKind};
use slang::Span;
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

            // Get method's postconditions;
            let posts = m.ensures();
            // Merge them into a single condition
            let post = posts
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            
            // Calculate obligation and error message (if obligation is not
            // verified)
            //println!("cmd {:#?}", &cmd);
            //println!("ivl {:#?}", &ivl);
            
            let (oblig, msg) = wp(&ivl, &post)?;
            //println!("Span {:#?}", Span::default());
            //println!("oblig {:#?}", &oblig);
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
        CmdKind::VarDefinition  { name, ty, expr }              => { if let Some(expr) = expr {Ok(IVLCmd::assign(name, expr))} // has expr 
                                                                     else {println!("Laver nop");Ok(IVLCmd::nop())} // doesn't have expr
                                                                    },
        CmdKind::Assignment     { name, expr }                  => Ok(IVLCmd::assign(name, expr)),
        CmdKind::Assume         { condition }                   => Ok(IVLCmd::assume(condition)),
        CmdKind::Loop           { invariants, variant, body}    => Ok(IVLCmd::_loop(invariants, variant, body)),
        CmdKind::Match          { body }                        => {    let mut cases = Vec::new();
                                                                        for i in 0..body.cases.len() {
                                                                            cases.push(cmd_to_ivlcmd(&Cmd::seq(&Cmd::assume(&body.cases[i].condition), &body.cases[i].cmd))?);
                                                                        }
                                                                        Ok(IVLCmd::nondets(&cases))
                                                                    }
        CmdKind::Return         { expr }                        => Ok(IVLCmd::_return(expr)),
        _ => todo!(" Not supported (yet)."),
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single
// assertion
fn wp(ivl: &IVLCmd, post: &Expr) -> Result<(Expr, String)> {
    //println!("Finding WP of {:#?} with expr: {:#?}", &ivl.kind, &expr_in.kind);
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message }       => Ok((condition.clone().and(&post), message.clone())),
        IVLCmdKind::Assume { condition }                => Ok((condition.clone().imp(&post), "Assume might fail".to_string())),
        IVLCmdKind::Seq(cmd1, cmd2)                     => { if !matches!(cmd1.kind, IVLCmdKind::Return{..}) {
                                                                let (expr2, msg2) = wp(cmd2, post)?;
                                                                let (expr1, msg1) = wp(cmd1, &expr2)?;
                                                                Ok((expr1,  msg2))
                                                            } else {
                                                                let IVLCmdKind::Return{ ref expr } = cmd1.kind else { todo!("Won't ever happen") };
                                                                if let Some(acc_expr) = expr {
                                                                    let mut temp_expr = Expr::bool(false);
                                                                    temp_expr.span = acc_expr.span;
                                                                    temp_expr.span = Span::from_start_end(temp_expr.span.start() - 7, temp_expr.span.end());
                                                                    Ok((temp_expr,  "Jeg er dum og mit return er ikke til sidst".to_string()))
                                                                } else {
                                                                    Ok((Expr::bool(false),  "Jeg er dum og mit return er ikke til sidst (no expr)".to_string()))
                                                                }
                                                            }
                                                            }
        IVLCmdKind::Assignment { name, expr }           => Ok((post.clone().subst(|x| x.is_ident(&name.ident), expr), ["Failed in assigning: ", &name.to_string(), " with expression ", &expr.to_string()].join(""))),//post[var -> expr]
        IVLCmdKind::Loop {invariants, variant, cases}   => { let mut precondition = Expr::bool(true);
                                                            for invariant in invariants.iter() {
                                                                precondition = invariant.clone().and(&precondition);
                                                            };
                                                            Ok((precondition.clone(), "Something wrong with the Loop yo".to_string()))// i && post
                                                            },
        IVLCmdKind::NonDet( cmd1, cmd2 )                => {let (expr0, msg0) = wp(cmd1, post)?;
                                                            let (expr1, msg1) = wp(cmd2, post)?;
                                                            Ok((expr0.clone().and(&expr1), msg0))
                                                            },
        IVLCmdKind::Return { expr }                     => {if let Some(expr) = expr {
                                                                let _message = ["Failed in returning expression: ", (&expr.to_string())].join("");
                                                                Ok((post.clone().subst(|x| matches!(x.kind, ExprKind::Result{..}), expr).clone(), _message.to_string()))
                                                            } else {
                                                                Ok((post.clone(), "Failed returning".to_string()))
                                                            }
                                                            },
        _ => todo!("Not supported (yet)."),
    }
}
