// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
/// TODO: IN PROGRESS



use std::io::Write;

use crate::kani_queries::QueryDb;
use lean_ast::lean_program::{LeanProgram, Function, Expr, Literal, Stmt, Type, BinaryOp, UnaryOp, Parameter, Hypothesis};
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::traversal::reverse_postorder;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, Const as mirConst, ConstOperand, ConstValue,
    HasLocalDecls, Local, Operand, Place, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind, UnOp, VarDebugInfoContents,
};
use rustc_middle::span_bug;
use rustc_middle::ty::layout::{
    HasParamEnv, HasTyCtxt, LayoutError, LayoutOf, LayoutOfHelpers, TyAndLayout,
};
use rustc_middle::ty::{self, Instance, IntTy, Ty, TyCtxt, UintTy};
use rustc_span::Span;
use rustc_target::abi::{HasDataLayout, TargetDataLayout};
use std::collections::hash_map::Entry;
use serde::de::Unexpected::Option;
use strum::IntoEnumIterator;
use tracing::{debug, debug_span, trace};

use super::kani_intrinsic::get_kani_intrinsic;


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
        let mut program = LeanProgram::new();
        LeanCtx { tcx, queries, program }
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
        let fcx = FunctionCtx::new(self, instance);
        let mut decl = fcx.codegen_declare_variables();
        let body = fcx.codegen_body();
        // pair body and a vector of hypothesis
        // pass as is to the constructor
        // decl.push(body);
        Some(Function::new(
            self.tcx.symbol_name(instance).name.to_string(),
            vec![],
            // todo: keep hypothesis separate?
            None,
            // todo: return type an option - 1) None - or 2) lean unit type
            None,
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
}

impl<'a, 'tcx> FunctionCtx<'a, 'tcx> {
    pub fn new(lcx: &'a LeanCtx<'tcx>, instance: Instance<'tcx>) -> FunctionCtx<'a, 'tcx> {
        // create names for all locals
        let mut local_names = FxHashMap::default();
        let mut name_occurrences: FxHashMap<String, usize> = FxHashMap::default();
        let mir = lcx.tcx.instance_mir(instance.def);
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
        Self { lcx, instance, mir, local_names }
    }

    //TODO: DONE! first pass
    fn codegen_declare_variables(&self) -> Vec<Stmt> {
        let ldecls = self.mir.local_decls();
        let decls: Vec<Stmt> = ldecls
            .indices()
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
                /// in lean declaration are implicit with the function name
                Some(Parameter::new (name, lean_type))
            })
            .collect();
        decls
    }

    //TODO: DONE! first pass
    fn codegen_type(&self, ty: Ty<'tcx>) -> Type {
        trace!(typ=?ty, "codegen_type");
        match ty.kind() {
            ty::Bool => Type::Bool,
            ty::Int(ity) => Type::Int,
            ty::Uint(uty) => Type::Nat,
            _ => todo!(),
        }
    }

    // TODO: Done first pass
    fn codegen_body(&self) -> Vec<Stmt> {
        let statements: Vec<Stmt> =
            reverse_postorder(self.mir).map(|(bb, bbd)| self.codegen_block(bb, bbd)).collect();
        statements
        //Stmt::Block { statements }
    }

    // TODO: Done first pass
    fn codegen_block(&self, bb: BasicBlock, bbd: &BasicBlockData<'tcx>) -> Stmt {
        debug!(?bb, ?bbd, "codegen_block");
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
    fn codegen_statement(&self, stmt: &Statement<'tcx>) -> Stmt {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                debug!(?place, ?rvalue, "codegen_statement");
                let rv = self.codegen_rvalue(rvalue);
                let place_name = self.local_name(place.local).clone();
                // assignment statement
                let asgn = Stmt::Assignment { variable: place_name, value: rv.1 };
                // add it to other statements generated while creating the rvalue (if any)
                add_statement(rv.0, asgn)
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


    // TODO: Done first pass
    /// Codegen an rvalue. Returns the expression for the rvalue and an optional
    /// statement for any possible checks instrumented for the rvalue expression
    fn codegen_rvalue(&self, rvalue: &Rvalue<'tcx>) -> (Option<Stmt>, Expr) {
        debug!(rvalue=?rvalue, "codegen_rvalue");
        match rvalue {
            Rvalue::Use(operand) => (None, self.codegen_operand(operand)),
            Rvalue::UnaryOp(op, operand) => self.codegen_unary_op(op, operand),
            Rvalue::BinaryOp(binop, box (lhs, rhs)) => self.codegen_binary_op(binop, lhs, rhs),
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

            BinyOp::Sub => Expr::BinaryOp { op: BinaryOp::Sub, left, right },
            BinOp::Mul => Expr::BinaryOp { op: BinaryOp::Mul, left, right },
            BinOp::Div => Expr::BinaryOp { op: BinaryOp::Div, left, right },

            BinOp::Neq => Expr::BinaryOp { op: BinaryOp::Neq, left, right },

            _ => todo!(),
        };
        (None, expr)
    }


    // TODO: Done first pass
    fn codegen_terminator(&self, term: &Terminator<'tcx>) -> Stmt {
        let _trace_span = debug_span!("CodegenTerminator", statement = ?term.kind).entered();
        debug!("handling terminator {:?}", term);
        match &term.kind {
            TerminatorKind::Call { func, args, destination, target, .. } => {
                self.codegen_funcall(func, args, destination, target, term.source_info.span)
            }
            TerminatorKind::Return => Stmt::Return,
            _ => todo!(),
        }
    }

    fn codegen_funcall(
        &self,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: &Place<'tcx>,
        target: &Option<BasicBlock>,
        span: Span,
    ) -> Stmt {
        debug!(?func, ?args, ?destination, ?span, "codegen_funcall");
        let fargs = self.codegen_funcall_args(args);
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
                        fargs,
                        *destination,
                        *target,
                        Some(span),
                    );
                }
                todo!()
            }
            _ => todo!(),
        }
    }

    //TODO:done one pass
    fn codegen_funcall_args(&self, args: &[Operand<'tcx>]) -> Vec<Expr> {
        debug!(?args, "codegen_funcall_args");
        args.iter()
            .filter_map(|o| {
                let ty = self.operand_ty(o);
                // TODO: handle non-primitive types
                if ty.is_primitive() {
                    return Some(self.codegen_operand(o));
                }
                // TODO: ignore non-primitive arguments for now (e.g. `msg`
                // argument of `kani::assert`)
                None
            })
            .collect()
    }

    //TODO:done one pass
    fn codegen_operand(&self, o: &Operand<'tcx>) -> Expr {
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

    //TODO:done one pass
    fn codegen_place(&self, place: &Place<'tcx>) -> Expr {
        debug!(place=?place, "codegen_place");
        debug!(place.local=?place.local, "codegen_place");
        debug!(place.projection=?place.projection, "codegen_place");
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
            (Scalar::Int(_), ty::Int) => Expr::Literal(Literal::Int(s.to_int().unwrap())),
            (Scalar::Int(_), ty::Uint) => Expr::Literal(Literal::Nat(s.to_int().unwrap())),
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



// TODO: done first pass
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