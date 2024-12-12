#![allow(unused)]

pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, PrefixOp, ExprKind, Type, Ident, Name, Range, Op, MethodRef, Var};
use slang::Span;
use slang_ui::prelude::*;
use std::env::var;
use std::sync::Arc;
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
            let mut pre = pres
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));

            let mut variant_var = None;

            if let Some(V) = m.variant.clone() {
                let mut gte_zero = V.ge(&Expr::num(0));
                gte_zero = fix_span(gte_zero, V.span);
                pre = pre.and(&gte_zero);
                variant_var = Some(V);
                //Figure out which input variable is being used in decrease
                /*for mut i in 0..m.args.len() {
                    let x = m.args[i].clone();
                    if let Some(iden) = e.as_ident() {
                        if x.name.ident.eq(iden) {
                            variant_var = i;
                        }
                    }
                }*/
            }
            
            // Convert the expression into an SMT expression
            let spre = pre.smt()?;
            // Assert precondition
            solver.assert(spre.as_bool()?)?;

            
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
            let post_correct_spans: Vec<(Expr, String)> = post
                .into_iter()
                .map(|(expr, msg)| (expr, msg))
                .collect();

            // Get method's body
            let cmd = &m.body.clone().unwrap().cmd;
            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(cmd, post_correct_spans.clone(), file, &variant_var)?;
            println!("Ivl: {}", ivl);
            /*fn adjust_span(mut expr: Expr) -> Expr {
                if (expr.span.start() > 8) {
                    expr.span = Span::from_start_end(expr.span.start() - 8, expr.span.end());
                }
                expr
            }*/

            //println!("post_correct_spans {:#?} ", post_correct_spans);
            
            // Calculate obligation and error message (if obligation is not
            // verified)
            //println!("cmd {:#?}", &cmd);
            //println!("ivl {:#?}", &ivl);
            
            let mut oblig = swp(&ivl, post_correct_spans)?;
            //println!("Span {:#?}", Span::default());
            //println!("oblig {:#?}", &oblig);
            // Convert obligation to SMT expression
            //println!("Out vec {:#?}", oblig);

            // Run the following solver-related statements in a closed scope.
            // That is, after exiting the scope, all assertions are forgotten
            // from subsequent executions of the solver
            
            // Loop over expr in oblig 
            //Tror vi skal loopp her
            let mut stop = false;
            oblig.reverse();
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
fn cmd_to_ivlcmd(cmd: &Cmd, post: Vec<(Expr, String)>, file: &slang::SourceFile, vari: &Option<Expr>) -> Result<IVLCmd> {
    //println!("cmd to ivlcmd {:#?}", &cmd.kind);
    match &cmd.kind {
        CmdKind::Assert         { condition, .. }               => Ok(IVLCmd::assert(condition, "Assert might fail!")),
        CmdKind::Seq            ( cmd1, cmd2)                   => Ok(IVLCmd::seq(&cmd_to_ivlcmd(cmd1, post.clone(), file, vari)?, 
                                                                                  &cmd_to_ivlcmd(cmd2, post.clone(), file, vari)?)),
        CmdKind::VarDefinition  { name, ty, expr }              => { if let Some(expr) = expr { // has expr 
                                                                        cmd_to_ivlcmd(&Cmd::assign(name, expr), post.clone(), file, vari)
                                                                     } else { // doesn't have expr
                                                                        Ok(IVLCmd::nop())
                                                                     }
                                                                    },
        CmdKind::Assignment     { name, expr }                  => Ok(IVLCmd::assign(name, expr)),
        CmdKind::Assume         { condition }                   => Ok(IVLCmd::assume(condition)),
        CmdKind::Loop           { invariants, variant, body}    => {let mut case_bodies = Vec::new();
                                                                    let mut all_invariants = Expr::bool(true);
                                                                    for i in 0..invariants.len() {
                                                                        all_invariants = all_invariants.and(&invariants[i]);
                                                                    }
                                                                    let mut all_condtions = Expr::bool(true);
                                                                    for i in 0..body.cases.len() {
                                                                        all_condtions = all_condtions.and(&body.cases[i].condition);
                                                                        case_bodies.push(cmd_to_ivlcmd(&body.cases[i].cmd, post.clone(), file, vari)?);
                                                                    }
                                                                    all_condtions = fix_span(all_condtions, all_invariants.span);
                                                                    
                                                                    let havoc_statement = find_assignments(cmd);

                                                                    let pre_loop = IVLCmd::seq(&IVLCmd::assert(&all_invariants, "Invariant might not hold on entry"), 
                                                                                                &IVLCmd::seq(&havoc_statement, &IVLCmd::assume(&all_invariants)));
                                                                    let loop_body1 = IVLCmd::seq(&IVLCmd::assume(&all_condtions),
                                                                                                 &IVLCmd::seqs(&case_bodies));
                                                                    let loop_body2 = IVLCmd::seq(&IVLCmd::assert(&all_invariants, "Invariant might not be preserved"),
                                                                                                 &IVLCmd::assume(&Expr::bool(false)));
                                                                    let loop_body = IVLCmd::seq(&loop_body1, &loop_body2);
                                                                    let encoded_loop = IVLCmd::nondet(&loop_body, &IVLCmd::assume(&all_condtions.prefix(PrefixOp::Not)));
                                                                    Ok(IVLCmd::seq(&pre_loop, &encoded_loop))},
        CmdKind::Match          { body }                        => {let mut cases = Vec::new();
                                                                    for i in 0..body.cases.len() {
                                                                        cases.push(cmd_to_ivlcmd(&Cmd::seq((&Cmd::assume(&body.cases[i].condition)),
                                                                                                             &body.cases[i].cmd), post.clone(), file , vari)?);
                                                                    }
                                                                    Ok(IVLCmd::nondets(&cases))
                                                                    }
        CmdKind::For            { name, range, body, .. }       => {let Range::FromTo(from, to) = range.clone();
                                                                    let assign = IVLCmd::assign(name, &from);
                                                                    let range_check = IVLCmd::assert(&Expr::op(&from, Op::Lt, &to), "Range start has to be less than range end");
                                                                    let ExprKind::Num(from_int) = from.kind else { todo!("Feature 4") };
                                                                    let ExprKind::Num(to_int) = to.kind else { todo!("Feature 4") };
                                                                    
                                                                    let body = cmd_to_ivlcmd(&body.cmd, post.clone(), file, vari)?;
                                                                    let inc = IVLCmd::assign(name, &Expr::op(&Expr::ident(&name.ident, &from.ty), Op::Add, &Expr::num(1)));
                                                                    let mut unrolled = Vec::new();
                                                                    unrolled.push(assign.clone());
                                                                    unrolled.push(range_check.clone());
                                                                    for i in from_int..to_int {
                                                                        unrolled.push(body.clone());
                                                                        unrolled.push(inc.clone());
                                                                    }
                                                                    //ast::Op::Gt => l.as_int()?.gt(r.as_int()?).into_dynamic(),
                                                                    Ok(IVLCmd::seqs(&unrolled))
                                                                    }
        CmdKind::Return         { expr }                        => {let mut ivl_cmd = IVLCmd::_return(expr);
                                                                    ivl_cmd.span = cmd.span;
                                                                    let mut seq = IVLCmd::seq(&ivl_cmd, &IVLCmd::assert(&post[0].0, &post[0].1));
                                                                    for i in 1..post.len() {
                                                                        seq = IVLCmd::seq(&seq, &IVLCmd::assert(&post[i].0, &post[i].1));
                                                                    }

                                                                    Ok(IVLCmd::seq(&seq, &IVLCmd::assume(&Expr::bool(false))))},
        CmdKind::MethodCall     { name, fun_name, args, method} => {//method fun_name(inp1, mul): Int
                                                                    //name = fun_name(args)
                                                                    // =>
                                                                    //a' = args
                                                                    //assert method.requires[x => a']
                                                                    //havoc name
                                                                    //assume method.ensures[x, Result => a', name]
                                                                    
                                                                    let mut input_arg_names = method.clone().get().unwrap().args.clone();
                                                                        
                                                                    if let Some(method_arc) = method.clone().get() {
                                                                        let identforreal = &method_arc.name.ident;
                                                                        
                                                                        let requires = method_arc.requires();
                                                                        let mut pre = requires
                                                                            .cloned()
                                                                            .reduce(|a, b| a & b)
                                                                            .unwrap_or(Expr::bool(true));

                                                                        let ensures = method_arc.ensures();
                                                                        let mut post = ensures
                                                                            .cloned()
                                                                            .reduce(|a, b| a & b)
                                                                            .unwrap_or(Expr::bool(true));

                                                                        let mut v = Expr::num(1);
                                                                        let mut subst_V = Expr::num(0);
                                                                        

                                                                        if let Some(V) = vari {
                                                                            v = V.clone();
                                                                            subst_V = V.clone();
                                                                            
                                                                            //decreased = fix_span(decreased, V.span);
                                                                            //pre = pre.and(&decreased);
                                                                        }
                                                                            
                                                                        // here we substitute the variables used in requires/ensures
                                                                        // so that we don't have name mismatching.
                                                                        // example:
                                                                        // method test(n: Int, m: Int)
                                                                        // requires n + n + m = 0
                                                                        // ensures m > 0
                                                                        for i in 0..input_arg_names.len() {
                                                                            let o_name = input_arg_names[i].name.ident.clone();
                                                                            input_arg_names[i].name.ident = input_arg_names[i].name.ident.postfix(&random_string());
                                                                            let mut expr = Expr::ident(&input_arg_names[i].name.ident, &input_arg_names[i].ty.1);
                                                                            expr.span = input_arg_names[i].ty.0;
                                                                            subst_V = subst_V.subst_ident(&o_name, &expr);
                                                                            pre = pre.subst_ident(&o_name, &expr);
                                                                            post = post.subst_ident(&o_name, &expr);
                                                                        }
                                                                        let mut mut_args = args.clone();
                                                                        let mut assigns = Vec::new();
                                                                        for i in 0..args.len() {
                                                                            //for i in range(len(args)) 
                                                                                //let randLetters() = args[i] (make assign)
                                                                                //args[i] -> a_new (use new var)
                                                                            // x = inc(x+1)
                                                                            // a = x+1
                                                                            // x = inc(a)
                                                                            //&Alphanumeric.sample_string(&mut rand::thread_rng(), 8).to_string()
                                                                            let new_name = Name { span: args[i].span, ident: Ident(random_string()) };
                                                                            let assign = IVLCmd::assign(&new_name, &args[i]);
                                                                            assigns.push(assign);
                                                                            let new_expr = Expr::ident(&new_name.ident, &args[i].ty);
                                                                            mut_args[i] = new_expr;
                                                                        }

                                                                        for i in 0..mut_args.len() {
                                                                            let expr = input_arg_names[i].clone();
                                                                            subst_V = subst_V.subst_ident(&expr.name.ident, &mut_args[i]);
                                                                            pre = pre.subst_ident(&expr.name.ident, &mut_args[i]);
                                                                            post = post.subst_ident(&expr.name.ident, &mut_args[i]);
                                                                        }
                                                                        let mut havoc = IVLCmd::nop();
                                                                        if let Some(name_acc) = name {
                                                                            if let Some((_, ty)) = &method_arc.return_ty {
                                                                                let mut name_expr = Expr::ident(&name_acc.  ident, &ty);
                                                                                name_expr.span = name_acc.span;
                                                                                post = post.subst_result(&name_expr);
                                                                                havoc = IVLCmd::assign(&name_acc, &Expr::ident(&name_acc.ident.postfix(&random_string()), &ty))
                                                                            }
                                                                        }
                                                                        let decrease = v.gt(&subst_V);
                                                                        let decrease_assert = IVLCmd::assert(&fix_span(decrease, cmd.span), "Termination messure might not decrease");
                                                                        pre = fix_span(pre, Span::from_start_end(fun_name.span.start(), cmd.span.end()));
                                                                        let assert_pre = IVLCmd::seq(&IVLCmd::assert(&pre, "Precondition of method might not hold"),
                                                                                                     &decrease_assert);
                                                                        let assume_post = IVLCmd::assume(&post);
                                                                        let call_part = IVLCmd::seq(&assert_pre, &IVLCmd::seq(&havoc, &assume_post));
                                                                        Ok(IVLCmd::seq(&IVLCmd::seqs(&assigns), &call_part))
                                                                    } else {
                                                                        Ok(IVLCmd::assert(&Expr::bool(false), "Method doesn't exists - L?"))
                                                                    }
                                                                    },
        any => todo!(" Not supported (yet) in IVLCmd. {:#?}", any),
    }
}

// Set *based* weakest precondition
fn swp<'a>(ivl: &IVLCmd, mut post: Vec<(Expr, String)>) -> Result<(Vec<(Expr, String)>)> {
    //println!("Finding wp..");
    //println!("Finding WP of {:#?} with expr: {:#?}", &ivl.kind, &expr_in.kind);
    match &ivl.kind {
        IVLCmdKind::Havoc { name, ty }                  => { Ok(post) }
        IVLCmdKind::Assert { condition, message }       => { post.push((condition.clone(), message.clone())); Ok(post) }
        IVLCmdKind::Assume { condition }                => { let mut new_post = Vec::new();
                                                             let mut new_condition = condition.clone();
                                                             for (post_expr, msg) in post.iter() {
                                                                new_condition = fix_span(new_condition, post_expr.span);
                                                                new_post.push((new_condition.imp(post_expr), msg.clone()))
                                                             }
                                                             Ok(new_post)
                                                            }
        IVLCmdKind::Seq(cmd1, cmd2)                     => {let post2 = swp(cmd2, post)?;   
                                                            let post1 = swp(cmd1, post2)?;
                                                            Ok(post1)
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
        any => todo!(" Not supported (yet) in swp. {:#?}", any),
    }
}

fn fix_span(mut expr_in: Expr, span: Span) -> Expr {
    match &expr_in.kind {
        ExprKind::Infix(e1, op, e2) => Expr::op(&fix_span(*e1.clone(), span), *op, &fix_span(*e2.clone(), span)),
        ExprKind::Prefix(op, e)     => fix_span(*e.clone(), span).prefix(*op),
        _                           => { expr_in.span = span.clone(); expr_in}
    }
}

use rand::distributions::{Alphanumeric, DistString};
fn find_assignments(cmd: &Cmd) -> IVLCmd {
    match &cmd.kind {                              // Same as havoc
        CmdKind::Assignment     {name, expr}    => IVLCmd::assign(name, &Expr::ident(&name.ident.postfix(&random_string()), &expr.ty)),
        CmdKind::Seq            (cmd1, cmd2)    => IVLCmd::seq(&find_assignments(cmd1), &find_assignments(cmd2)),
        CmdKind::Match          { body }        => {let mut out = IVLCmd::nop();
                                                    for case in body.cases.iter() {
                                                        out = IVLCmd::seq(&out, &find_assignments(&case.cmd))
                                                    };
                                                    out
                                                    }
        CmdKind::Loop           { body, .. }    => { let mut out = IVLCmd::nop();
                                                    for case in body.cases.iter() {
                                                        out = IVLCmd::seq(&out, &find_assignments(&case.cmd));
                                                    };
                                                    out
                                                    },
        _                                         => IVLCmd::nop()
    }
} 
//Is not used
fn find_readings(expr: &Expr) -> IVLCmd {
    match &expr.kind {                              // Same as havoc
        ExprKind::Ident(ident)      => IVLCmd::assign(&Name {span: expr.span, ident: ident.clone()}, &Expr::ident(&ident.postfix(&random_string()), &expr.ty)),
        ExprKind::Infix(e1, op, e2) => IVLCmd::seq(&find_readings(e1), &find_readings(e2)),
        ExprKind::Prefix(op, e)     => find_readings(e),
        _                           => IVLCmd::nop()
    }
} 

fn random_string() -> String {
    Alphanumeric.sample_string(&mut rand::thread_rng(), 8).to_string()
}