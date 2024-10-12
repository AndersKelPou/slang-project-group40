pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Op, Ident};
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
        CmdKind::Assert { condition, .. } => Ok(IVLCmd::assert(condition, "Assert might fail!")),
        CmdKind::Seq(cmd1, cmd2) => Ok(IVLCmd::seq(&cmd_to_ivlcmd(cmd1)?, &cmd_to_ivlcmd(cmd2)?)),
        //CmdKind::Return { expr } => Ok(IVLCmd::)
        CmdKind::Assignment { name, expr } => Ok(IVLCmd::assign(name, expr)),
        _ => todo!(" Not supported (yet)."),
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single
// assertion
fn wp(ivl: &IVLCmd, expr_in: &Expr) -> Result<(Expr, String)> {
    //println!("Finding WP of {:#?} with expr: {:#?}", &ivl.kind, &expr_in.kind);
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => Ok((Expr::op(&condition.clone(), Op::And, &expr_in), message.clone())),
        IVLCmdKind::Seq(cmd1, cmd2) => {let (expr2, msg2) = wp(cmd2, expr_in)?;
                                        let (expr1, msg1) = wp(cmd1, &expr2)?;
                                        Ok((expr1,  msg1 ))}, // should not be just msg1
        IVLCmdKind::Assignment { name, expr } => Ok((expr_in.clone().subst(|x| x.is_ident(&name.ident), expr), name.to_string())),//expr_in[var -> expr]
        _ => todo!("Not supported (yet)."),
    }
}
