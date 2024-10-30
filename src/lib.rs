#![allow(unused)]

pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, PrefixOp, ExprKind};
use slang::Span;
use slang_ui::prelude::*;
use std::collections::HashSet;
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
            let mut post: Vec<(Expr, String)> = posts
                .cloned()
                .map(|expr| (
                    expr.clone(),
                    format!("Error ensuring the property {}", expr),
                ))
                .collect();
                
            if post.is_empty() {
                post.push((Expr::bool(true), "Default post condition".to_string()));
            }
            /*fn adjust_span(mut expr: Expr) -> Expr {
                if (expr.span.start() > 8) {
                    expr.span = Span::from_start_end(expr.span.start() - 8, expr.span.end());
                }
                expr
            }*/
            
            let post_correct_spans: Vec<(Expr, String)> = post
                .into_iter()
                .map(|(expr, msg)| (expr, msg))
                .collect();

            //println!("post_correct_spans {:#?} ", post_correct_spans);
            
            // Calculate obligation and error message (if obligation is not
            // verified)
            println!("cmd {:#?}", &cmd);
            //println!("ivl {:#?}", &ivl);
            
            let oblig = swp(&ivl, post_correct_spans)?;
            //println!("Span {:#?}", Span::default());
            //println!("oblig {:#?}", &oblig);
            // Convert obligation to SMT expression
            println!("Out vec {:#?}", oblig);

            // Run the following solver-related statements in a closed scope.
            // That is, after exiting the scope, all assertions are forgotten
            // from subsequent executions of the solver
            
            // Loop over expr in oblig 
            //Tror vi skal loopp her
            let mut stop = false;
            for mut i in 0..oblig.len() {
                if (stop) {
                    break;
                } 
                solver.scope(|solver| {
                    let mut or_oblig = Expr::bool(false);
                    let mut last_obl = Expr::bool(false); let mut last_msg = String::new();
                    for (obl, msg) in oblig[0..i+1].iter() {
                        or_oblig = or_oblig.or(&obl.prefix(PrefixOp::Not));
                        last_obl.span = obl.span.clone();
                        last_msg = msg.clone()
                    }
                    if let Ok(soblig) = or_oblig.smt() { 
                        solver.assert(soblig.as_bool()?)?;
                        //println!("we asserted right");
                        // Run SMT solver on all csdurrent assertionsasd
                        match solver.check_sat()? {
                            // If the obligations result not validasd, report the error (on
                            // the span in which the error happens)
                            smtlib::SatResult::Sat => {
                                cx.error(last_obl.span, format!("{last_msg}"));
                                stop = true;
                            }
                            smtlib::SatResult::Unknown => {
                                cx.warning(last_obl.span, "{msg}: unknown sat result");
                            }
                            smtlib::SatResult::Unsat => (),
                        }
                    } else { // Er Ok() altid en success? eller kan det også være en error? forstår det ikke (seriøst), det kan ikke være en error hvis det er Ok()
                        println!("Failed with {:#?}", or_oblig);
                        todo!("Smt failed to generate(somehow???????)")
                    }
                    // Check validity of obligation
                    //println!("smt_obligation {:#?} ", soblig);
                    //println!("smt_obligation as bool {:#?} ", soblig.as_bool());
    
                    //First loop iter oblig[0]
                    //Second loop iter oblig[0..1]
                    //Third loop iter oblig[0..2]
                    //...
                    Ok(())
                })?;
            }
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
        CmdKind::Loop           { invariants, variant, body}    => {let mut case_bodies = Vec::new();
                                                                    let mut all_invariants = Expr::bool(true);
                                                                    for i in 0..invariants.len() {
                                                                        all_invariants = all_invariants.and(&invariants[i]);
                                                                        //cases.push(cmd_to_ivlcmd(&Cmd::seq((&Cmd::assume(&body.cases[i].condition)), &body.cases[i].cmd))?);
                                                                    }
                                                                    let mut all_condtions = Expr::bool(true);
                                                                    for i in 0..body.cases.len() {
                                                                        all_condtions = all_condtions.and(&body.cases[i].condition);
                                                                        case_bodies.push(cmd_to_ivlcmd(&body.cases[i].cmd)?);
                                                                    }
                                                                    all_condtions = fix_span(all_condtions, all_invariants.span);
                                                                    //case_bodies = fix_span(case_bodies, all_invariants.span);
                                                                    let assert_statement = IVLCmd::assert(&all_invariants, "Invariant might not hold");
                                                                    //TODO add havoc of all vars changed between assert and assume:
                                                                    let pre_loop = IVLCmd::seq(&assert_statement, &IVLCmd::assume(&all_invariants));
                                                                    let loop_body1 = IVLCmd::seq(&IVLCmd::assume(&all_condtions),
                                                                                                 &IVLCmd::seqs(&case_bodies));
                                                                    let loop_body2 = IVLCmd::seq(&assert_statement,
                                                                                                 &IVLCmd::assume(&Expr::bool(false)));
                                                                    let loop_body = IVLCmd::seq(&loop_body1, &loop_body2);
                                                                    let encoded_loop = IVLCmd::nondet(&loop_body, &IVLCmd::assume(&all_condtions.prefix(PrefixOp::Not)));
                                                                    Ok(IVLCmd::seq(&pre_loop, &encoded_loop))},
        CmdKind::Match          { body }                        => {let mut cases = Vec::new();
                                                                    for i in 0..body.cases.len() {
                                                                        cases.push(cmd_to_ivlcmd(&Cmd::seq((&Cmd::assume(&body.cases[i].condition)), &body.cases[i].cmd))?);
                                                                    }
                                                                    Ok(IVLCmd::nondets(&cases))
                                                                    }
        CmdKind::Return         { expr }                        => {let mut ivl_cmd = IVLCmd::_return(expr); ivl_cmd.span = cmd.span; Ok(ivl_cmd)},
        _ => todo!(" Not supported (yet)."),
    }
}

// Set *based* weakest precondition
fn swp<'a>(ivl: &IVLCmd, mut post: Vec<(Expr, String)>) -> Result<(Vec<(Expr, String)>)> {
    println!("Finding wp..");
    //println!("Finding WP of {:#?} with expr: {:#?}", &ivl.kind, &expr_in.kind);
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message }       => { post.push((condition.clone(), message.clone())); Ok(post) }
        IVLCmdKind::Assume { condition }                => { let mut new_post = Vec::new();
                                                             let mut new_condition = condition.clone();
                                                             for (post_expr, msg) in post.iter() {
                                                                new_condition = fix_span(new_condition, post_expr.span);
                                                                new_post.push((new_condition.imp(post_expr), msg.clone()))
                                                             }
                                                             Ok(new_post)
                                                            }
        IVLCmdKind::Seq(cmd1, cmd2)                     => { if !matches!(cmd1.kind, IVLCmdKind::Return{..}) {
                                                                let post2 = swp(cmd2, post)?;   
                                                                let post1 = swp(cmd1, post2)?;
                                                                Ok(post1)
                                                            } else {
                                                                let IVLCmdKind::Return{ ref expr } = cmd1.kind else { todo!("Won't ever happen") };
                                                                let mut temp_expr = Expr::bool(false);
                                                                temp_expr.span = cmd1.span;
                                                                Ok(vec![(temp_expr, "Return not at end of program".to_string())])
                                                            }
                                                            }
        IVLCmdKind::Assignment { name, expr }           => {let mut new_post = Vec::new();
                                                            for (post_expr, msg) in post.iter() { 
                                                                let mut new_expr = expr.clone();
                                                                new_expr = fix_span(new_expr, post_expr.span.clone());
                                                                new_post.push((post_expr.clone().subst(|x| x.is_ident(&name.ident), &new_expr), msg.to_string()));
                                                            }
                                                            Ok(new_post) //post[var -> expr]
                                                            }
        IVLCmdKind::NonDet( cmd1, cmd2 )                => {let mut post1 = swp(cmd1, post.clone())?;
                                                            let post2 = swp(cmd2, post.clone())?;
                                                            post1.extend(post2);
                                                            Ok(post1)
                                                            },
        IVLCmdKind::Return { expr }                     => {if let Some(acc_expr) = expr {
                                                                let mut new_post = Vec::new();
                                                                for (post_expr, msg) in post.iter() { 
                                                                    let _message = msg.to_string();//["Failed in returning expression: ", (&acc_expr.to_string())].join("");
                                                                    let mut new_acc_expr = acc_expr.clone();
                                                                    new_acc_expr = fix_span(new_acc_expr, post_expr.span.clone());
                                                                    new_post.push((post_expr.clone().subst(|x| matches!(x.kind, ExprKind::Result{..}), &new_acc_expr).clone(), _message.to_string()));
                                                                }
                                                                Ok(new_post)
                                                            } else { Ok(post) }
                                                            },
        _ => todo!("Not supported (yet)."),
    }
}


//Expr_infex(Expr(A, span), Expr(0, span), span);

fn fix_span(mut expr_in: Expr, span: Span) -> Expr {
    match &expr_in.kind {
        ExprKind::Infix(e1, op, e2) => Expr::op(&fix_span(*e1.clone(), span), *op, &fix_span(*e2.clone(), span)),
        ExprKind::Prefix(op, e)     => fix_span(*e.clone(), span).prefix(*op),
        _                           => { expr_in.span = span.clone(); expr_in}
    }
    
}