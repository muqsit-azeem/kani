// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
/// TODO: IN PROGRESS



use std::io::Write;

use crate::kani_queries::QueryDb;
use lean_ast::lean_program::{LeanProgram, Function, Expr, Literal, Stmt, Type, BinaryOp, UnaryOp, Parameter, Hypothesis, Variable};
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::traversal::reverse_postorder;
use rustc_middle::mir::{BasicBlock, BasicBlockData, BinOp, Body, Const as mirConst, ConstOperand, ConstValue, HasLocalDecls, Local, Operand, Place, ProjectionElem, Rvalue, Statement, StatementKind, SwitchTargets, Terminator, TerminatorKind, UnOp, VarDebugInfoContents};

use rustc_middle::{mir, span_bug};
use rustc_middle::ty::layout::{
    HasParamEnv, HasTyCtxt, LayoutError, LayoutOf, LayoutOfHelpers, TyAndLayout,
};
use rustc_middle::ty::{self, Instance, InstanceDef, IntTy, List, Ty, TyCtxt, UintTy};
use rustc_span::Span;
use rustc_target::abi::{Abi, HasDataLayout, TargetDataLayout};
// use std::iter;
use std::collections::hash_map::Entry;
use std::collections::HashSet;
// use std::intrinsics::mir::BasicBlock;
use itertools::Itertools;
// use serde::de::Unexpected::Option;
// use strum::IntoEnumIterator;
use tracing::{debug, debug_span, trace};

use super::kani_intrinsic::{get_kani_intrinsic};

/// A context that provides the main methods for translating MIR constructs to
/// Lean and stores what has been codegen so far
pub struct LeanCtx<'tcx> {
    /// the typing context
    pub tcx: TyCtxt<'tcx>,
    /// a snapshot of the query values. The queries shouldn't change at this point,
    /// so we just keep a copy.
    pub queries: QueryDb,
    /// the Lean program
    program: LeanProgram,
}


impl<'tcx> LeanCtx<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, queries: QueryDb) -> LeanCtx<'tcx> {
        let program = LeanProgram::new();
        LeanCtx { tcx, queries, program}
    }



    // Todo: Clarify this
    /// Codegen a function into a lean function.
    /// Returns `None` if the function is a hook. ---?
    pub fn codegen_function(&self, instance: Instance<'tcx>) -> Option<Function> {
        debug!(?instance, "lean_codegen_function");
        if get_kani_intrinsic(self.tcx, instance).is_some() {
            debug!("skipping kani intrinsic `{instance}`");
            return None;
        }
        let mut fcx = FunctionCtx::new(self, instance);
        let decl = fcx.codegen_declare_variables();
        let body = fcx.codegen_body();
        // let ret_temp = fcx.current_fn_typ();
        let ret = fcx.codegen_type(fcx.current_fn_typ());
        // let ret = if ret_temp.is_unit() {
        //     None
        // } else {
        //     Some(ret_temp)
        // };

        // pair body and a vector of hypothesis
        // pass as is to the constructor
        // decl.push(body);
        Some(Function::new(
            self.tcx.symbol_name(instance).name.to_string(),
            decl,
            // todo: keep hypothesis separate? --  no these are just parameters
            None,
            //todo: return type an option - For specific cases now, hardcoded Except with String and Unit Type
            // however, in general, return type \alpha means we return Except String \alpha
            Some(ret),
            body,
        )
        )
    }

    pub fn add_function(&mut self, function: Function) {
        self.program.add_function(function);
    }

    /// Write the program to the given writer
    pub fn write<T: Write>(&self, writer: &mut T) -> std::io::Result<()> {
        self.program.write_to(writer)?;
        Ok(())
    }
}

pub(crate) struct FunctionCtx<'a, 'tcx> {
    lcx: &'a LeanCtx<'tcx>,
    instance: Instance<'tcx>,
    mir: &'a Body<'tcx>,
    /// Maps from local to the name of the corresponding Lean variable.
    local_names: FxHashMap<Local, String>,

    /// A map to keep track of the source of each borrow. This is an ugly hack
    /// borrowed from boogie backend, e.g.
    /// ```
    /// let b = &mut x;
    /// ````
    /// In this case, the map will contain an entry that maps `b` to `x`
    pub(crate) ref_to_expr: FxHashMap<Place<'tcx>, Expr>,
    visited_blocks: HashSet<BasicBlock>,
}

impl<'a, 'tcx> FunctionCtx<'a, 'tcx> {

    pub fn new(lcx: &'a LeanCtx<'tcx>, instance: Instance<'tcx>) -> FunctionCtx<'a, 'tcx> {
        // create names for all locals
        let mut local_names = FxHashMap::default();
        let mut name_occurrences: FxHashMap<String, usize> = FxHashMap::default();
        let mir = lcx.tcx.instance_mir(instance.def);
        // Initialize visited_blocks as empty
        let visited_blocks = HashSet::new();
        let ldecls = mir.local_decls();
        for local in ldecls.indices() {
            let debug_info = mir.var_debug_info.iter().find(|info| match info.value {
                VarDebugInfoContents::Place(p) => p.local == local && p.projection.len() == 0,
                VarDebugInfoContents::Const(_) => false,
            });
            let name = if let Some(debug_info) = debug_info {
                let base_name = format!("{}", debug_info.name);
                let entry = name_occurrences.entry(base_name.clone());
                let name = match entry {
                    Entry::Occupied(mut o) => {
                        let occ = o.get_mut();
                        let index = *occ;
                        *occ += 1;
                        format!("{base_name}_{}", index)
                    }
                    Entry::Vacant(v) => {
                        v.insert(1);
                        base_name
                    }
                };
                name
            } else {
                format!("{local:?}")
            };
            local_names.insert(local, name);
        }

        Self { lcx, instance, mir, local_names, ref_to_expr: FxHashMap::default(), visited_blocks, }
    }

    // fn codegen_declare_variables(&self) -> Vec<Parameter> {
    //     let ldecls = self.mir.local_decls();
    //     let decls: Vec<Parameter> = ldecls
    //         .indices()
    //         .filter_map(|lc| {
    //             let typ = self.instance.instantiate_mir_and_normalize_erasing_regions(
    //                 self.tcx(),
    //                 ty::ParamEnv::reveal_all(),
    //                 ty::EarlyBinder::bind(ldecls[lc].ty),
    //             );
    //             // skip ZSTs
    //             if self.layout_of(typ).is_zst() {
    //                 return None;
    //             }
    //             debug!(?lc, ?typ, "codegen_declare_variables");
    //             let name = self.local_name(lc).clone();
    //             let lean_type = self.codegen_type(typ);
    //             /// in lean declaration are implicit with the function name
    //             Some(Parameter::new (name, lean_type))
    //         })
    //         .collect();
    //     decls
    // }
    fn codegen_declare_variables(&self) -> Vec<Parameter> {
        let ldecls = self.mir.local_decls();
        // the number of function arguments excluding the return value
        let num_params = self.mir.arg_count;
        let decls: Vec<Parameter> = ldecls
            .indices()
            .filter(|&lc| lc.index() > 0 && lc.index() <= num_params) //Filter to include only parameters (excluding the return placeholder)
            .filter_map(|lc| {
                let typ = self.instance.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx(),
                    ty::ParamEnv::reveal_all(),
                    ty::EarlyBinder::bind(ldecls[lc].ty),
                );
                // skip ZSTs
                if self.layout_of(typ).is_zst() {
                    return None;
                }
                debug!(?lc, ?typ, "codegen_declare_variables");
                let name = self.local_name(lc).clone();
                let lean_type = self.codegen_type(typ);
                // in lean declaration are implicit with the function name
                Some(Parameter::new(name, lean_type))
            })
            .collect();
        decls
    }


    //TODO: DONE! first pass
    fn codegen_type(&self, ty: Ty<'tcx>) -> Type {
        trace!(typ=?ty, "codegen_type");
        match ty.kind() {
            ty::Bool => Type::Bool,
            ty::Int(_ity) => Type::Int,
            ty::Uint(_uty) => Type::Nat,
            ty::Tuple(types) => {
                //TODO: Only handles first element of tuple for now (e.g.
                // ignores overflow field of an addition and only takes the
                // result field)
                self.codegen_type(types.iter().next().unwrap())
            }
            ty::Adt(def, args) => {
                let name = format!("{def:?}");
                if name == "kani::array::Array" {
                    let fields = def.all_fields();
                    //let mut field_types: Vec<Type> = fields.filter_map(|f| {
                    //    let typ = f.ty(self.tcx(), args);
                    //    self.layout_of(typ).is_zst().then(|| self.codegen_type(typ))
                    //}).collect();
                    //assert_eq!(field_types.len(), 1);
                    //let typ = field_types.pop().unwrap();
                    let phantom_data_field = fields
                        .filter(|f| self.layout_of(f.ty(self.tcx(), args)).is_zst())
                        .exactly_one()
                        .unwrap_or_else(|_| panic!());
                    let phantom_data_type = phantom_data_field.ty(self.tcx(), args);
                    assert!(phantom_data_type.is_phantom_data());
                    let field_type = args.types().exactly_one().unwrap_or_else(|_| panic!());
                    let typ = self.codegen_type(field_type);
                    Type::user_defined(String::from("Array"), vec![typ])
                } else {
                    todo!()
                }
            }
            ty::Ref(_r, ty, m) => {
                if m.is_not() {
                    return self.codegen_type(*ty);
                }
                else {
                    //TODO: Fix this
                    return self.codegen_type(*ty);
                }

            }
            _ => todo!(),
        }
    }

    // TODO: Done first pass
    // fn codegen_body(&mut self) -> Vec<Stmt> {
    //     let statements: Vec<Stmt> =
    //         reverse_postorder(self.mir).map(|(bb, bbd)| self.codegen_block(bb, bbd)).collect();
    //     statements
    //     //Stmt::Block { statements }
    // }

    // codegen_body without map
    fn codegen_body(&mut self) -> Vec<Stmt> {
        let mut statements = Vec::new();
        let ldecls = self.mir.local_decls();
        // the number of function arguments excluding the return value
        let num_params = self.mir.arg_count;
        let mut decls_stmt: Vec<Stmt> = Vec::new();

        for lc in ldecls.indices() {
            let typ = self.instance.instantiate_mir_and_normalize_erasing_regions(
                self.tcx(),
                ty::ParamEnv::reveal_all(),
                ty::EarlyBinder::bind(ldecls[lc].ty),
            );

            // Skip ZST
            if self.layout_of(typ).is_zst() {
                continue;
            }

            debug!(?lc, ?typ, "initialize_variables");
            let name = self.local_name(lc).clone();
            let lean_type = self.codegen_type(typ);

            // a default value based on type
            let val: String = match lean_type {
                Type::Bool => "true".to_string(),
                Type::Nat => "0".to_string(),
                Type::Int => "1".to_string(),
                Type::Unit | Type::ParameterType { .. } | Type::FunctionType { .. } | Type::Product { .. } => {
                    todo!()
                },
                Type::UserDefined { .. } => "#[0]".to_string(),
            };

            if lc.index() == 0 || lc.index() > num_params {
                let stmt = Stmt::Assignment {
                    variable: name,
                    typ: Some(lean_type),
                    value: Expr::Variable { name: val },
                };
                decls_stmt.push(stmt);
            }
            else {
                let stmt = Stmt::Assignment {
                    variable: name.clone(),
                    typ: Some(lean_type),
                    value: Expr::Variable { name },
                };
                decls_stmt.push(stmt);
            }
        }

        statements.extend(decls_stmt);
        for (bb, bbd) in reverse_postorder(self.mir) {
            if !self.visited_blocks.contains(&bb) {
                println!("Generating code for block number: {:?}", bb); // Print the block number
                statements.push(self.codegen_block(bb, bbd)); // Generate the statement and collect it
            } else {
                println!("SKIPPING regeneration of code for block number: {:?}", bb);
            }
        }
        statements
    }

    fn codegen_block(&mut self, bb: BasicBlock, bbd: &BasicBlockData<'tcx>) -> Stmt {
        debug!(?bb, ?bbd, "codegen_block");
        // println!("{:?} {:?} {}", bb, bbd, "CODEGEN BLOCK");
        // the first statement should be labelled. if there is no statements, then the
        // terminator should be labelled.
        let statements = match bbd.statements.len() {
            0 => {
                let term = bbd.terminator();
                let tcode = self.codegen_terminator(term);
                vec![tcode]
            }
            _ => {
                let mut statements: Vec<Stmt> =
                    bbd.statements.iter().map(|stmt| self.codegen_statement(stmt)).collect();

                let term = self.codegen_terminator(bbd.terminator());
                statements.push(term);
                statements
            }
        };
        Stmt::Block { statements }
    }

    // TODO: Done first pass
    fn codegen_statement(&mut self, stmt: &Statement<'tcx>) -> Stmt {
        match &stmt.kind {
            // StatementKind::Assign(box (place, rvalue)) => {
            //     debug!(?place, ?rvalue, "codegen_statement");
            //     let rv = self.codegen_rvalue(rvalue);
            //     let place_name = self.local_name(place.local).clone();
            //     // assignment statement
            //     let asgn = Stmt::Assignment { variable: place_name, value: rv.1 };
            //     // add it to other statements generated while creating the rvalue (if any)
            //     add_statement(rv.0, asgn)
            // }
            //TODO: if the statement has Lvalue kani_instrinsics Array
            // e.g., a[index]=val
            // then codegen as follows:
            // 1. a:= a.set! index val
            StatementKind::Assign(box (place, rvalue)) => {

                debug!(?place, ?rvalue, "codegen_statement");
                let place_name = self.local_name(place.local).clone();
                println!("PLACE NAME: {}", place_name);
                if (place_name == "_9") {
                    println!("PLACE NAME: {}", place_name);
                }
                if let Rvalue::Ref(_, _, rhs) = rvalue {
                    let expr = self.codegen_place(rhs);
                    self.ref_to_expr.insert(*place, expr);
                    // todo: remove (for debugging specific example)
                    //
                    // if place_name == "_5" {
                    //     Stmt::Skip
                    // } else if place_name == "_7" {
                    //     Stmt::Skip
                    // }
                    // else { todo!() }
                    Stmt::Skip
                } else if is_deref(place) {
                    //todo: consider other cases
                    // Only Kani intrinsic Arrays are covered
                    // lookup the place itself
                    debug!(?self.ref_to_expr, ?place, ?place.local, "codegen_statement_assign_deref");
                    let empty_projection = List::empty();
                    let place = Place { local: place.local, projection: empty_projection };
                    let mut place_name = self.local_name(place.local).clone();
                    // this gets the name to be used for array.
                    if let Some(expr) = self.ref_to_expr.get(&place) {
                        match expr {
                            Expr::Select { base, .. } => match &**base {
                                Expr::Field { base: field_base, .. } => match &**field_base {
                                    Expr::Variable { name, .. } => {
                                        place_name = name.to_string();
                                    },
                                    _ => {},
                                },
                                _ => {},
                            },
                            _ => {},
                        }
                    }

                    let expr = self.ref_to_expr.get(&place).unwrap();
                    let rv = self.codegen_rvalue(rvalue);
                    //let asgn = Stmt::Assignment { variable: expr.to_string(), value: rv.1 };
                    println!("PLACE NAME {}", place_name);
                    println!("EXPR NAME {}", expr.to_string());
                    let asgn = Stmt::ArrayAssignment { variable: place_name, var_exp: expr.to_string(), value: rv.1 };
                    add_statement(rv.0, asgn)
                } else {
                    // println!("PLACE NAME: {}", place_name);
                    let rv = self.codegen_rvalue(rvalue);
                    // let new_place_name = if place_name == *self.local_name(Place::from(mir::RETURN_PLACE).local) {
                    //     format!("let {}", place_name)
                    // } else {
                    //     place_name
                    // };
                    // let new_place =  &*String::from("let")  + place_name + &*String::from("let");
                    let asgn = Stmt::Assignment { variable: place_name, typ:None, value: rv.1 };
                    // let asgn = Stmt::Assignment { variable: new_place_name, typ:None, value: rv.1 };
                    // add it to other statements generated while creating the rvalue (if any)
                    add_statement(rv.0, asgn)
                }
            }

            _ => todo!()
            // StatementKind::FakeRead(..)
            // | StatementKind::SetDiscriminant { .. }
            // | StatementKind::Deinit(..)
            // | StatementKind::StorageLive(..)
            // | StatementKind::StorageDead(..)
            // | StatementKind::Retag(..)
            // | StatementKind::PlaceMention(..)
            // | StatementKind::AscribeUserType(..)
            // | StatementKind::Coverage(..)
            // | StatementKind::Intrinsic()
            // | StatementKind::ConstEvalCounter
            // | StatementKind::Nop => todo!(),
        }
    }


    // /// Generates Lean for MIR [TerminatorKind::SwitchInt].
    // /// Operand evaluates to an integer;
    // /// executes depending on its value to one of the targets, and otherwise fallback to `targets.otherwise()`.
    // /// The otherwise value is stores as the last value of targets.
    // fn codegen_switch_int(
    //     &mut self,
    //     discr: &Operand,
    //     targets: &SwitchTargets,
    //     loc: Location,
    // ) -> Stmt {
    //     let v = self.codegen_operand_stable(discr);
    //     let switch_ty = v.typ().clone();
    //
    //     // Switches with empty branches should've been eliminated already.
    //     assert!(targets.len() > 1);
    //     if targets.len() == 2 {
    //         // Translate to a guarded goto
    //         let (case, first_target) = targets.branches().next().unwrap();
    //         Stmt::IfThenElse {}
    //
    //
    //         Stmt::block(
    //             vec![
    //                 v.eq(Expr::int_constant(case, switch_ty)).if_then_else(
    //                     Stmt::goto(bb_label(first_target), loc),
    //                     None,
    //                     loc,
    //                 ),
    //                 Stmt::goto(bb_label(targets.otherwise()), loc),
    //             ],
    //             loc,
    //         )
    //     } else {
    //         let cases = targets
    //             .branches()
    //             .map(|(c, bb)| {
    //                 Expr::int_constant(c, switch_ty.clone())
    //                     .switch_case(Stmt::goto(bb_label(bb), loc))
    //             })
    //             .collect();
    //         let default = Stmt::goto(bb_label(targets.otherwise()), loc);
    //         v.switch(cases, Some(default), loc)
    //     }
    // }

    fn codegen_switch_int(& mut self, discr: &Operand<'tcx>, targets: &SwitchTargets) -> Stmt {
        debug!(discr=?discr, targets=?targets, "codegen_switch_int");
        let op = self.codegen_operand(discr);
        println!("targets length {}", targets.iter().len());
        if targets.all_targets().len() == 2 {
            let then = targets.iter().next().unwrap();
            self.visited_blocks.insert(then.1);
            let bbd_then = self.mir.basic_blocks[then.1].clone();
            let then_statements = match bbd_then.statements.len() {
                0 => {
                    let term = bbd_then.terminator();
                    let tcode = self.codegen_terminator(term);
                    vec![tcode]
                }
                _ => {
                    let mut then_statements: Vec<Stmt> = Vec::new();

                    for stmt in &bbd_then.statements {
                        println!("ADDING then_statements");
                        let codegen_stmt = self.codegen_statement(stmt);
                        then_statements.push(codegen_stmt);
                    }


                    if then_statements.is_empty() {
                        println!("then_statements is empty");
                    } else {
                        println!("then_statements is NOT empty{}", then_statements.len());
                    }
                    let term = self.codegen_terminator(bbd_then.terminator());
                    then_statements.push(term);
                    if then_statements.is_empty() {
                        println!("then_statements is empty");
                    } else {
                        println!("then_statements is NOT empty {}", then_statements.len());
                    }
                    println!("Generating code for THEN block number: {:?}", then.1);
                    // then_statements.push(Stmt::Assignment {
                    //     variable: "y".to_string(),
                    //     typ: None,
                    //     value: Expr::Literal(Literal::Int(2.into()))});
                    then_statements
                }
            };
            let bbd_else = self.mir.basic_blocks[targets.otherwise()].clone();
            self.visited_blocks.insert(targets.otherwise());
            let else_statements = match bbd_else.statements.len() {
                0 => {
                    let term = bbd_else.terminator();
                    let tcode = self.codegen_terminator(term);
                    vec![tcode]
                }
                _ => {

                    let mut else_statements: Vec<Stmt> =
                        bbd_else.statements.iter().map(|stmt| self.codegen_statement(stmt)).collect();
                    let term = self.codegen_terminator(bbd_else.terminator());
                    if else_statements.is_empty() {
                        println!("else_statements is empty");
                    } else {
                        println!("else_statements is NOT empty {}", else_statements.len());
                    }
                    else_statements.push(term);
                    // match bbd_else.terminator().kind {
                    //     TerminatorKind::Goto {target} => todo!(),
                    //     TerminatorKind::SwitchInt { ref targets, .. } => todo!(),
                    //     TerminatorKind::UnwindResume => todo!(),
                    //     TerminatorKind::UnwindTerminate(_) => todo!(),
                    //     TerminatorKind::Return => todo!(),
                    //     TerminatorKind::Unreachable => todo!(),
                    //     TerminatorKind::Drop { .. } => todo!(),
                    //     TerminatorKind::Call { .. } => todo!(),
                    //     TerminatorKind::Assert { .. } => todo!(),
                    //     TerminatorKind::Yield { .. } => todo!(),
                    //     TerminatorKind::CoroutineDrop => todo!(),
                    //     TerminatorKind::FalseEdge { .. } => todo!(),
                    //     TerminatorKind::FalseUnwind { .. } => todo!(),
                    //     TerminatorKind::InlineAsm { .. } => todo!(),
                    // }

                    //return: bbk, success: bbj

                    // else_statements.push(Stmt::Assignment {
                    //     variable: "y".to_string(),
                    //     typ: None,
                    //     value: Expr::Literal(Literal::Int(2.into()))});
                    if else_statements.is_empty() {
                        println!("else_statements is empty");
                    } else {
                        println!("else_statements is NOT empty {}", else_statements.len());
                    }
                    println!("Generating code for ELSE block number: {:?}", targets.otherwise());
                    else_statements
                }
            };

            let right = match self.operand_ty(discr).kind() {
                ty::Bool => Literal::Bool(then.0 != 0),
                ty::Uint(_) => Literal::Nat(then.0.into()),
                _ => unreachable!(),
            };
            // model as an if
        //     return Stmt::IfThenElse {
        //         cond: Expr::BinaryOp {
        //             op: BinaryOp::Eq,
        //             left: Box::new(op),
        //             right: Box::new(Expr::Literal(right)),
        //         },
        //         // then_branch: Box::new(Stmt::Goto { label: format!("{:?}", then.1) }),
        //
        //         //todo: I want to do codegenstatements here,
        //         // however, I have a block
        //         // So, I can do something like -- Block {statments}
        //
        //         then_branch: Box::new(Stmt::Block { statements }),
        //         else_branch: Some(Box::new(Stmt::Block { statements }),
        //     };
        // }
        // todo!()

        return Stmt::IfThenElse {
            cond: Expr::BinaryOp {
                op: BinaryOp::Eq,
                left: Box::new(op),
                right: Box::new(Expr::Literal(right)),
            },
            then_branch: Box::new(Stmt::Block { statements: then_statements }),
            else_branch: Some(Box::new(Stmt::Block { statements: else_statements })),
        };
    }
    todo!()
    }



    // TODO: Done first pass
    /// Codegen an rvalue. Returns the expression for the rvalue and an optional
    /// statement for any possible checks instrumented for the rvalue expression
    fn codegen_rvalue(&self, rvalue: &Rvalue<'tcx>) -> (Option<Stmt>, Expr) {
        debug!(rvalue=?rvalue, "codegen_rvalue");
        match rvalue {
            Rvalue::Use(operand) => (None, self.codegen_operand(operand)),
            Rvalue::UnaryOp(op, operand) => self.codegen_unary_op(op, operand),
            Rvalue::BinaryOp(binop, box (lhs, rhs)) => self.codegen_binary_op(binop, lhs, rhs),
            Rvalue::CheckedBinaryOp(binop, box (ref e1, ref e2)) => {
                // TODO: handle overflow check
                self.codegen_binary_op(binop, e1, e2)
            }
            _ => todo!(),
        }
    }

    // TODO: Done first pass
    fn codegen_unary_op(&self, op: &UnOp, operand: &Operand<'tcx>) -> (Option<Stmt>, Expr) {
        debug!(op=?op, operand=?operand, "codegen_unary_op");
        let o = self.codegen_operand(operand);
        let expr = match op {
            UnOp::Not => {
                Expr::UnaryOp { op: UnaryOp::Not, operand: Box::new(o) }
            },
            UnOp::Neg => {
                Expr::UnaryOp { op: UnaryOp::Neg, operand: Box::new(o) }
            }
        };
        (None, expr)
    }


    // TODO: Done first pass
    fn codegen_binary_op(
        &self,
        binop: &BinOp,
        lhs: &Operand<'tcx>,
        rhs: &Operand<'tcx>,
    ) -> (Option<Stmt>, Expr) {
        debug!(binop=?binop, "codegen_binary_op");
        let left = Box::new(self.codegen_operand(lhs));
        let right = Box::new(self.codegen_operand(rhs));
        let expr = match binop {
            BinOp::Eq => Expr::BinaryOp { op: BinaryOp::Eq, left, right },
            BinOp::AddUnchecked | BinOp::Add => Expr::BinaryOp { op: BinaryOp::Add, left, right },
            BinOp::Lt => Expr::BinaryOp { op: BinaryOp::Lt, left, right },
            BinOp::Gt => Expr::BinaryOp { op: BinaryOp::Gt, left, right },
            BinOp::Le => Expr::BinaryOp { op: BinaryOp::Lte, left, right },
            BinOp::Ge => Expr::BinaryOp { op: BinaryOp::Gte, left, right },

            // BinOp::And => Expr::BinaryOp { op: BinaryOp::And, left, right },
            // BinOp::Or => Expr::BinaryOp { op: BinaryOp::Or, left, right },

            BinOp::Sub => Expr::BinaryOp { op: BinaryOp::Sub, left, right },
            BinOp::Mul => Expr::BinaryOp { op: BinaryOp::Mul, left, right },
            BinOp::Div => Expr::BinaryOp { op: BinaryOp::Div, left, right },

            BinOp::Ne => Expr::BinaryOp { op: BinaryOp::Neq, left, right },

            _ => todo!(),
        };
        (None, expr)
    }

    fn current_fn_typ(&self) -> Ty<'tcx>{
        debug!("Current function type{:?}: ",self.fn_sig_of_instance(self.instance).skip_binder().output());
        self.fn_sig_of_instance(self.instance).skip_binder().output()
    }

    // TODO: fix assert within ifthen else fail here
    fn codegen_terminator(& mut self, term: &Terminator<'tcx>) -> Stmt {
        let _trace_span = debug_span!("CodegenTerminator", statement = ?term.kind).entered();
        debug!("handling terminator {:?}", term);
        match &term.kind {
            TerminatorKind::Call { func, args, destination, target, .. } => {
                self.codegen_funcall(func, args, destination, target, term.source_info.span)
            }
            TerminatorKind::SwitchInt { discr, targets } => self.codegen_switch_int(discr, targets),
            TerminatorKind::Goto { target } => self.codegen_block(*target, &self.mir.basic_blocks[*target]),
            TerminatorKind::Return => {
                // let rty = self.fn_sig_of_instance(self.instance).skip_binder().output();
                let rty = self.current_fn_typ();
                if rty.is_unit() {
                    // todo: Stmt::Return Unit???
                    Stmt::Skip
                } else {
                    let p = Place::from(mir::RETURN_PLACE);
                    //Stmt::Return {expr: Expr::ExceptOk}
                    Stmt::Return { expr: self.codegen_place(&p) }
                }
            },
            TerminatorKind::Assert { .. } => Stmt::Skip, // TODO: ignore injection assertions for now
            _ => todo!(),
        }
    }

    // fn codegen_ret_unit(&mut self) -> Stmt {
    //     let is_file_local = false;
    //     let ty = self.codegen_ty_unit();
    //     let var = self.ensure_global_var(
    //         FN_RETURN_VOID_VAR_NAME,
    //         is_file_local,
    //         ty,
    //         Location::none(),
    //         |_, _| None,
    //     );
    //     Stmt::ret(Some(var), Location::none())
    // }

    pub fn fn_sig_of_instance(&self, instance: Instance<'tcx>) -> ty::PolyFnSig<'tcx> {
        let fntyp = instance.ty(self.tcx(), ty::ParamEnv::reveal_all());
            match fntyp.kind() {
            ty::Closure(_def_id, _subst) => todo!(),
            ty::FnDef(..) => {
                let sig = fntyp.fn_sig(self.tcx());
                // todo: Calls through vtable or Fn pointer for an ABI that may require untupled arguments.
                // if self.ty_needs_untupled_args(fntyp) {
                //     return self.sig_with_untupled_args(sig);
                // }
                sig
            }
            ty::FnPtr(..) => todo!(),
            ty::Coroutine(_did, _args, _) => todo!(),
            _ => unreachable!("Can't get function signature of type: {:?}", fntyp),
        }
    }

    fn codegen_funcall(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: &Place<'tcx>,
        target: &Option<BasicBlock>,
        span: Span,
    ) -> Stmt {
        debug!(?func, ?args, ?destination, ?span, "codegen_funcall");
        let funct = self.operand_ty(func);
        // TODO: Only Kani intrinsics are handled currently
        match &funct.kind() {
            ty::FnDef(defid, substs) => {
                let instance = Instance::expect_resolve(
                    self.tcx(),
                    ty::ParamEnv::reveal_all(),
                    *defid,
                    substs,
                );

                if let Some(intrinsic) = get_kani_intrinsic(self.tcx(), instance) {
                    return self.codegen_kani_intrinsic(
                        intrinsic,
                        instance,
                        args,
                        *destination,
                        *target,
                        Some(span),
                    );
                }
                let fargs = self.codegen_funcall_args(args);


                // `symbol_name` will contain the name of the function
                // if let ty::FnDef(defid, _) = funct.kind() {
                // let mut symbol_name = self.tcx().def_path_str(*defid);
                let symbol_name = self.tcx().symbol_name(instance).name.to_string();
                let mut stmts: Vec<Stmt> = match instance.def {
                    // Here an empty drop glue is invoked; we just ignore it.
                    // InstanceDef::DropGlue(_, None) => {
                    //     return Stmt::goto(self.current_fn().find_label(&target.unwrap()), loc);
                    // }
                    // // Handle a virtual function call via a vtable lookup
                    // InstanceDef::Virtual(def_id, idx) => {
                    //     let self_ty = self.operand_ty(&args[0]);
                    //     self.codegen_virtual_funcall(
                    //         self_ty,
                    //         def_id,
                    //         idx,
                    //         destination,
                    //         &mut fargs,
                    //         loc,
                    //     )
                    // }
                    // Normal, non-virtual function calls
                    InstanceDef::Item(..) => {
                        // We need to handle FnDef items in a special way because `codegen_operand` compiles them to dummy structs.
                        // (cf. the function documentation)
                        // let func_exp = self.codegen_func_expr(instance, None);
                        // vec![
                        //     self.codegen_expr_to_place(destination, func_exp.call(fargs)),
                        // ]
                        // vec![Stmt::function_call(symbol_name, fargs)]
                        vec![Stmt::Assignment {variable: self.local_name(destination.local).clone(), typ: None, value: Expr::function_call(symbol_name, fargs)}]
                        // vec![]
                    }
                    _ => todo!(),
                    // InstanceDef::DropGlue(_, Some(_))
                    // | InstanceDef::FnPtrAddrShim(_, _)
                    // | InstanceDef::Intrinsic(..)
                    // | InstanceDef::FnPtrShim(..)
                    // | InstanceDef::VTableShim(..)
                    // | InstanceDef::ReifyShim(..)
                    // | InstanceDef::ClosureOnceShim { .. }
                    // | InstanceDef::CloneShim(..) => {
                    //     // We need to handle FnDef items in a special way because `codegen_operand` compiles them to dummy structs.
                    //     // (cf. the function documentation)
                    //     let func_exp = self.codegen_func_expr(instance, None);
                    //     vec![
                    //         self.codegen_expr_to_place(destination, func_exp.call(fargs))
                    //             .with_location(loc),
                    //     ]
                    // }
                    // InstanceDef::ThreadLocalShim(_) => todo!(),
                };
                // the way MIR is designed for function call, it will always have a return block
                // stmts.push(self.codegen_block(target.unwrap(), &self.mir.basic_blocks[target.unwrap()]));
                stmts.push(Stmt::Skip);
                Stmt::block(stmts)
            }


                // // let loc = self.codegen_span(&span);
                // let funct = self.operand_ty(func);
                // let mut fargs = self.codegen_funcall_args(args);
                // match &funct.kind() {
                //     ty::FnDef(defid, subst) => {
                //         let instance =
                //             Instance::resolve(self.tcx(), ty::ParamEnv::reveal_all(), *defid, subst)
                //                 .unwrap()
                //                 .unwrap();
                //
                //         // if self.ty_needs_untupled_args(funct) {
                //         //     self.codegen_untupled_args(instance, &mut fargs, args.last());
                //         // }
                //
                //         // if let Some(hk) = self.hooks.hook_applies(self.tcx, instance) {
                //         //     return hk.handle(self, instance, fargs, *destination, *target, Some(span));
                //         // }
                //
                //         let mut stmts: Vec<Stmt> = match instance.def {
                //             // Here an empty drop glue is invoked; we just ignore it.
                //             // InstanceDef::DropGlue(_, None) => {
                //             //     return Stmt::goto(self.current_fn().find_label(&target.unwrap()), loc);
                //             // }
                //             // // Handle a virtual function call via a vtable lookup
                //             // InstanceDef::Virtual(def_id, idx) => {
                //             //     let self_ty = self.operand_ty(&args[0]);
                //             //     self.codegen_virtual_funcall(
                //             //         self_ty,
                //             //         def_id,
                //             //         idx,
                //             //         destination,
                //             //         &mut fargs,
                //             //         loc,
                //             //     )
                //             // }
                //             // Normal, non-virtual function calls
                //             InstanceDef::Item(..) => {
                //                 // We need to handle FnDef items in a special way because `codegen_operand` compiles them to dummy structs.
                //                 // (cf. the function documentation)
                //                 let func_exp = self.codegen_func_expr(instance, None);
                //                 vec![
                //                     self.codegen_expr_to_place(destination, func_exp.call(fargs)),
                //                 ]
                //             }
                //             _ => todo!(),
                //             // InstanceDef::DropGlue(_, Some(_))
                //             // | InstanceDef::FnPtrAddrShim(_, _)
                //             // | InstanceDef::Intrinsic(..)
                //             // | InstanceDef::FnPtrShim(..)
                //             // | InstanceDef::VTableShim(..)
                //             // | InstanceDef::ReifyShim(..)
                //             // | InstanceDef::ClosureOnceShim { .. }
                //             // | InstanceDef::CloneShim(..) => {
                //             //     // We need to handle FnDef items in a special way because `codegen_operand` compiles them to dummy structs.
                //             //     // (cf. the function documentation)
                //             //     let func_exp = self.codegen_func_expr(instance, None);
                //             //     vec![
                //             //         self.codegen_expr_to_place(destination, func_exp.call(fargs))
                //             //             .with_location(loc),
                //             //     ]
                //             // }
                //             // InstanceDef::ThreadLocalShim(_) => todo!(),
                //         };
                //         todo!()
                //         // stmts.push(self.codegen_end_call(target.as_ref(), loc));
                //         //Stmt::block(stmts)
                //     }
                //     _ => todo!()
                //     // Function call through a pointer
                //     // ty::FnPtr(_) => {
                //     //     let func_expr = self.codegen_operand(func).dereference();
                //     //     // Actually generate the function call and return.
                //     //     Stmt::block(
                //     //         vec![
                //     //             self.codegen_expr_to_place(destination, func_expr.call(fargs))
                //     //                 .with_location(loc),
                //     //             Stmt::goto(self.current_fn().find_label(&target.unwrap()), loc),
                //     //         ],
                //     //         loc,
                //     //     )
                //     // }
                //     // x => unreachable!("Function call where the function was of unexpected type: {:?}", x),
                // }
            //     todo!()
            // }



            _ => todo!(),
        }
    }

    // fn codegen_end_call(&self, target: Option<&BasicBlock>) -> Stmt {
    //     if let Some(next_bb) = target {
    //         Stmt::goto(self.current_fn().find_label(next_bb))
    //     } else {
    //         todo!()
    //     }
    // }


    // /// Generate a goto expression that references the function identified by `instance`.
    // ///
    // /// Note: In general with this `Expr` you should immediately either `.address_of()` or `.call(...)`.
    // ///
    // /// This should not be used where Rust expects a "function item" (See `codegen_fn_item`)
    // pub fn codegen_func_expr(&mut self, instance: Instance<'tcx>, span: Option<&Span>) -> Expr {
    //     let (func_symbol, func_typ) = self.codegen_func_symbol(instance);
    //     Expr::symbol_expression(func_symbol.name, func_typ)
    // }


    // fn codegen_func_symbol(&mut self, instance: Instance<'tcx>) -> (&Symbol, Type) {
    //     let funct = self.codegen_function_sig(self.fn_sig_of_instance(instance));
    //     let sym = if self.tcx().is_foreign_item(instance.def_id()) {
    //         // Get the symbol that represents a foreign instance.
    //         self.codegen_foreign_fn(instance)
    //     } else {
    //         // All non-foreign functions should've been declared beforehand.
    //         trace!(func=?instance, "codegen_func_symbol");
    //         let func = self.symbol_name(instance);
    //         self.symbol_table()
    //             .lookup(&func)
    //             .unwrap_or_else(|| panic!("Function `{func}` should've been declared before usage"))
    //     };
    //     (sym, funct)
    // }




    //TODO:done one pass
    fn codegen_funcall_args(&mut self, args: &[Operand<'tcx>]) -> Vec<Expr> {
        debug!(?args, "codegen_funcall_args");
        for o in args.iter() {
            let ty = self.operand_ty(o);
            debug!(?ty, "Argument type");
            //debug!(, "TYPEKIND");
        }
        let fargs = args.iter()
            .filter_map(|o| {
                let ty = self.operand_ty(o);
                // TODO: handle non-primitive types
                if ty.is_primitive() {
                    return Some(self.codegen_operand(o));
                }
                //TODO: very specific -- generalize for any bit count, i8,u8,i64,i128,...
                if ty.to_string() == "kani::array::Array<i32>" {
                    // match o {
                    //     Operand::Copy(place) | Operand::Move(place) => {
                    //         if let Some(operand_name) =  {
                    //             println!("Operand refers to: {}", operand_name);
                    //         }
                    //     }
                    //     Operand::Constant(constant) => {
                    //         // For constants, you might want to extract the constant's value or type
                    //         println!("Operand is a constant: {:?}", constant);
                    //     }
                    // }
                    return Some(Expr::Variable {name: self.local_name(o.place().unwrap().local).clone()});
                }

                // else if matches!(ty, kani::array::Array) {
                // // else if matches!(ty.kind(),KaniIntrinsic::KaniAnyArray) {
                //
                // }

                // let intrinsic = get_kani_intrinsic(self.tcx(), instance);

                // TODO: ignore non-primitive arguments for now (e.g. `msg`
                // argument of `kani::assert`)
                None
            })
            .collect();
            debug!(?fargs, "codegen_funcall_fargs");
            fargs
    }




    // pub(crate) fn codegen_funcall_args(
    //     &mut self,
    //     args: &[Operand<'tcx>],
    //     skip_zst: bool,
    // ) -> Vec<Expr> {
    //     let fargs = args
    //         .iter()
    //         .filter_map(|o| {
    //             let op_ty = self.operand_ty(o);
    //             if op_ty.is_bool() {
    //                 Some(self.codegen_operand(o).cast_to(Type::c_bool()))
    //             } else if !self.is_zst(op_ty) || !skip_zst {
    //                 Some(self.codegen_operand(o))
    //             } else {
    //                 // We ignore ZST types.
    //                 debug!(arg=?o, "codegen_funcall_args ignore");
    //                 None
    //             }
    //         })
    //         .collect();
    //     debug!(?fargs, "codegen_funcall_args");
    //     fargs
    // }

    //TODO:done second pass
    pub(crate) fn codegen_operand(&self, o: &Operand<'tcx>) -> Expr {
        trace!(operand=?o, "codegen_operand");
        // A MIR operand is either a constant (literal or `const` declaration)
        // or a place (being moved or copied for this operation).
        // An "operand" in MIR is the argument to an "Rvalue" (and is also used
        // by some statements.)
        match o {
            Operand::Copy(place) | Operand::Move(place) => self.codegen_place(place),
            Operand::Constant(c) => self.codegen_constant(c),
        }
    }


    // TODO:done second pass
    // fn codegen_place(&self, place: &Place<'tcx>) -> Expr {
    //     debug!(place=?place, "codegen_place");
    //     debug!(place.local=?place.local, "codegen_place");
    //     debug!(place.projection=?place.projection, "codegen_place");
    //     self.codegen_local(place.local)
    // }


    pub(crate) fn codegen_place(&self, place: &Place<'tcx>) -> Expr {
        debug!(place=?place, "codegen_place");
        debug!(place.local=?place.local, "codegen_place");
        debug!(place.projection=?place.projection, "codegen_place");
        if let Some(expr) = self.ref_to_expr.get(place) {
            return expr.clone();
        }
        //let local_ty = self.mir.local_decls()[place.local].ty;
        self.codegen_local(place.local)
    }

    fn codegen_local(&self, local: Local) -> Expr {
        // TODO: handle function definitions
        Expr::Variable { name: self.local_name(local).clone() }
    }

    fn local_name(&self, local: Local) -> &String {
        &self.local_names[&local]
    }

    fn codegen_constant(&self, c: &ConstOperand<'tcx>) -> Expr {
        trace!(constant=?c, "codegen_constant");
        // TODO: monomorphize
        match c.const_ {
            mirConst::Val(val, ty) => self.codegen_constant_value(val, ty),
            _ => todo!(),
        }
    }


    // TODO: done first pass
    fn codegen_constant_value(&self, val: ConstValue<'tcx>, ty: Ty<'tcx>) -> Expr {
        debug!(val=?val, "codegen_constant_value");
        match val {
            ConstValue::Scalar(s) => self.codegen_scalar(s, ty),
            _ => todo!(),
        }
    }

    // TODO: done first pass
    fn codegen_scalar(&self, s: Scalar, ty: Ty<'tcx>) -> Expr {
        debug!(kind=?ty.kind(), "codegen_scalar");
        match (s, ty.kind()) {
            (Scalar::Int(_), ty::Bool) => Expr::Literal(Literal::Bool(s.to_bool().unwrap())),
            (Scalar::Int(_), ty::Int(it)) => match it {
                IntTy::I8 => Expr::Literal(Literal::Int(s.to_i8().unwrap().into())),
                IntTy::I16 => Expr::Literal(Literal::Int(s.to_i16().unwrap().into())),
                IntTy::I32 => Expr::Literal(Literal::Int(s.to_i32().unwrap().into())),
                IntTy::I64 => Expr::Literal(Literal::Int(s.to_i64().unwrap().into())),
                IntTy::I128 => Expr::Literal(Literal::Int(s.to_i128().unwrap().into())),
                IntTy::Isize => Expr::Literal(Literal::Int(s.to_target_isize(self).unwrap().into())),
            },
            (Scalar::Int(_), ty::Uint(it)) => match it {
                UintTy::U8 => Expr::Literal(Literal::Nat(s.to_u8().unwrap().into())),
                UintTy::U16 => Expr::Literal(Literal::Nat(s.to_u16().unwrap().into())),
                UintTy::U32 => Expr::Literal(Literal::Nat(s.to_u32().unwrap().into())),
                UintTy::U64 => Expr::Literal(Literal::Nat(s.to_u64().unwrap().into())),
                UintTy::U128 => Expr::Literal(Literal::Nat(s.to_u128().unwrap().into())),
                UintTy::Usize => Expr::Literal(Literal::Nat(s.to_target_usize(self).unwrap().into())),
            },

            // (Scalar::Int(_), ty::Bool) => Expr::Literal(Literal::Bool(s.to_bool().unwrap())),
            // // TODO: CHANGE TO BV
            // // TODO: get target width
            // //(Scalar::Int(_), ty::Int(_)) => Expr::Literal(Literal::Int(s.to_int().into())),
            // // // TODO: get target width
            // //(Scalar::Int(_), ty::Uint(_)) => Expr::Literal(Literal::Nat(s.to_int().unwrap().into())),
            // //_ => todo!(),
            //
            // (Scalar::Int(_), ty::Int(it)) => match it {
            //     // IntTy::I8 => Expr::Literal(Literal::Int(s.to_i8().unwrap().into())),
            //     // IntTy::I16 => Expr::Literal(Literal::Int(s.to_i16().unwrap().into())),
            //     // IntTy::I32 => Expr::Literal(Literal::Int(s.to_i32().unwrap().into())),
            //     // IntTy::I64 => Expr::Literal(Literal::Int(s.to_i64().unwrap().into())),
            //     // IntTy::I128 => Expr::Literal(Literal::Int(s.to_i128().unwrap().into())),
            //     IntTy::Isize => {
            //         // TODO: get target width
            //         Expr::Literal(Literal::Int(s.to_target_isize(self).unwrap().into()))
            //     }
            //     _ => todo!()
            // },
            // (Scalar::Int(_), ty::Uint(it)) => match it {
            //     // UintTy::U8 => Expr::Literal(Literal::bv(8, s.to_u8().unwrap().into())),
            //     // UintTy::U16 => Expr::Literal(Literal::bv(16, s.to_u16().unwrap().into())),
            //     // UintTy::U32 => Expr::Literal(Literal::bv(32, s.to_u32().unwrap().into())),
            //     // UintTy::U64 => Expr::Literal(Literal::bv(64, s.to_u64().unwrap().into())),
            //     // UintTy::U128 => Expr::Literal(Literal::bv(128, s.to_u128().unwrap().into())),
            //     UintTy::Usize => {
            //         // TODO: get target width
            //         Expr::Literal(Literal::Nat(s.to_target_usize(self).unwrap().into()))
            //     }
            //     _ => todo!()
            // },
            _ => todo!(),



        }
    }

    // TODO: done first pass
    fn operand_ty(&self, o: &Operand<'tcx>) -> Ty<'tcx> {
        // TODO: monomorphize
        o.ty(self.mir.local_decls(), self.lcx.tcx)
    }
}

impl<'a, 'tcx> LayoutOfHelpers<'tcx> for FunctionCtx<'a, 'tcx> {
    type LayoutOfResult = TyAndLayout<'tcx>;

    fn handle_layout_err(&self, err: LayoutError<'tcx>, span: Span, ty: Ty<'tcx>) -> ! {
        span_bug!(span, "failed to get layout for `{}`: {}", ty, err)
    }
}

impl<'a, 'tcx> HasParamEnv<'tcx> for FunctionCtx<'a, 'tcx> {
    fn param_env(&self) -> ty::ParamEnv<'tcx> {
        ty::ParamEnv::reveal_all()
    }
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for FunctionCtx<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.lcx.tcx
    }
}

impl<'a, 'tcx> HasDataLayout for FunctionCtx<'a, 'tcx> {
    fn data_layout(&self) -> &TargetDataLayout {
        self.lcx.tcx.data_layout()
    }
}


/// Create a new statement that includes `s1` (if non-empty) in statements block `s2`
fn add_statement(s1 :Option<Stmt>, s2: Stmt) -> Stmt {
    match s1 {
        Some(s1) => match s1 {
            Stmt::Block { mut statements } => {
                statements.push(s2);
                Stmt::Block { statements }
            }
            _ => Stmt::Block { statements: vec![s1, s2] },
        }
        None => s2
    }
}


fn is_deref(p: &Place<'_>) -> bool {
    let proj = p.projection;
    if proj.len() == 1 && proj.iter().next().unwrap() == ProjectionElem::Deref {
        return true;
    }
    false
}