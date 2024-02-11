// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module is for handling Kani intrinsics, i.e. items whose implementation
//! is defined in the Kani compiler. These items are defined in the `kani`
//! library and are annotated with a `rustc_diagnostic_item`.

use super::lean_ctx::FunctionCtx;

use lean_ast::lean_program::{Expr, Stmt, Theorem, Parameter, Hypothesis, Variable};
use rustc_middle::mir::{BasicBlock, Operand, Place};
use rustc_middle::ty::{Instance, TyCtxt};
use rustc_span::Span;
use std::str::FromStr;
use strum::VariantNames;
use strum_macros::{EnumString, EnumVariantNames};
use tracing::debug;
use lean_ast::lean_program::Expr::{ExceptError, UnaryOp};
use lean_ast::lean_program::Literal::Int;
use lean_ast::lean_program::Stmt::{Return};
use lean_ast::lean_program::UnaryOp::{Not};


// TODO: move this enum up to `kani_middle`
#[derive(Debug, Clone, PartialEq, Eq, EnumString, EnumVariantNames)]
pub enum KaniIntrinsic {
    /// Kani assert statement (`kani::assert`)
    KaniAssert,

    /// Kani assume statement (`kani::assume`)
    KaniAssume,

    /// Kani unbounded array (`kani::array::any_array`)
    KaniAnyArray,

    /// `kani::array::Array::len`
    KaniAnyArrayLen,

    /// `Index<usize> for kani::array::Array`
    KaniAnyArrayIndex,

    /// `IndexMut<usize> for kani::array::Array`
    KaniAnyArrayIndexMut,
}


/// If provided function is a Kani intrinsic (e.g. assert, assume, cover), returns it
// TODO: move this function up to `kani_middle` along with the enum
pub fn get_kani_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> Option<KaniIntrinsic> {
    for intrinsic in KaniIntrinsic::VARIANTS {
        let attr_sym = rustc_span::symbol::Symbol::intern(intrinsic);
        if let Some(attr_id) = tcx.all_diagnostic_items(()).name_to_id.get(&attr_sym) {
            if instance.def.def_id() == *attr_id {
                debug!("matched: {:?} {:?}", attr_id, attr_sym);
                return Some(KaniIntrinsic::from_str(intrinsic).unwrap());
            }
        }
    }
    None
}

//todo: Clarify this again
impl<'a, 'tcx> FunctionCtx<'a, 'tcx> {


    pub fn codegen_kani_intrinsic(
        &mut self,
        intrinsic: KaniIntrinsic,
        instance: Instance<'tcx>,
        fargs: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        target: Option<BasicBlock>,
        span: Option<Span>,
    ) -> Stmt
    //todo: (None, Hypothesis) or (Theorem, None) or both
    {
        match intrinsic {
            KaniIntrinsic::KaniAssert => {
                self.codegen_kani_assert(instance, fargs, assign_to, target, span)
            }
            KaniIntrinsic::KaniAssume => {
                self.codegen_kani_assume(instance, fargs, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyArray => {
                self.codegen_kani_any_array(instance, fargs, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyArrayLen => {
                self.codegen_kani_any_array_len(instance, fargs, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyArrayIndex => {
                self.codegen_kani_any_array_index(instance, fargs, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyArrayIndexMut => {
                self.codegen_kani_any_array_index_mut(instance, fargs, assign_to, target, span)
            }
        }
    }

    pub fn codegen_kani_assert(
        &self,
        _instance: Instance<'tcx>,
        fargs: &[Operand<'tcx>],
        _assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert_eq!(fargs.len(), 2);
        let expr = self.codegen_operand(&fargs[0]);
        // let expr = fargs.remove(0);
        // TODO: handle message
        // TODO: handle location
        let stmt = Stmt::IfThenElse { cond: UnaryOp {op: Not, operand: Box::new(expr) } , then_branch: Box::new(Return {expr: ExceptError}), else_branch: None };
        stmt
    }

    // TODO: Hypothesis as an input
    pub fn codegen_kani_assume(
        &self,
        _instance: Instance<'tcx>,
        fargs: &[Operand<'tcx>],
        _assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        //TODO: Adapt this for assume either using Result or Except
        assert_eq!(fargs.len(), 1); // 2);
        let expr = self.codegen_operand(&fargs[0]);
        //let expr = fargs.remove(0);
        let stmt = Stmt::IfThenElse { cond: UnaryOp {op: Not, operand: Box::new(expr) } , then_branch: Box::new(Return {expr: ExceptError}), else_branch: None };
        stmt
    }


    fn codegen_kani_any_raw(
        &self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert!(args.is_empty());

        let place = self.codegen_place(&assign_to);

        let symbol = if let Expr::Variable { name } = place {
            name
        } else {
            panic!("expecting place to be a symbol and not {place:?}.")
        };

        Stmt::block(vec![
            //TODO:
            // Stmt::Havoc { name: symbol },
            // Stmt::Declaration { name: "Array".to_string(), typ: None, expr: Expr::Variable { name: "x".to_string() } },
            // Stmt::Goto { label: format!("{:?}", target.unwrap()) },
            Stmt::Skip
        ])
    }


    fn codegen_kani_any_array(
        &self,
        instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        target: Option<BasicBlock>,
        span: Option<Span>,
    ) -> Stmt {
        assert!(args.is_empty());

        self.codegen_kani_any_raw(instance, args, assign_to, target, span)
    }




    fn codegen_kani_any_array_len(
        &self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert_eq!(args.len(), 1);
        debug!(?args, "codegen_kani_any_array_len");

        let self_ref = &args[0];
        let expr = self
            .operand_to_expr(self_ref)
            .expect("expecting operand to be a ref to an existing expression");
        let len = Expr::Field { base: Box::new(expr.clone()), field: String::from(".size") };

        let place = self.codegen_place(&assign_to);

        let Expr::Variable { name } = place else { panic!("expecting place to be a symbol") };

        Stmt::Assignment { variable: name, value: len }
    }



    fn codegen_kani_any_array_index(
        &self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert_eq!(args.len(), 2);
        debug!(?args, "codegen_kani_any_array_index");

        let self_ref = &args[0];
        let expr = self
            .operand_to_expr(self_ref)
            .expect("expecting operand to be a ref to an existing expression");
        // let map = Expr::Field { base: Box::new(expr.clone()), field: String::from("data") };
        let map = Expr::Field { base: Box::new(expr.clone()), field: String::from(".get! ") };

        let index = self.codegen_operand(&args[1]);
        let index_expr = Expr::Select { base: Box::new(map), key: Box::new(index) };

        let place = self.codegen_place(&assign_to);

        let Expr::Variable { name } = place else { panic!("expecting place to be a symbol") };

        Stmt::Assignment { variable: name, value: index_expr }
    }

    fn codegen_kani_any_array_index_mut(
        &mut self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert_eq!(args.len(), 2);
        debug!(?args, "codegen_kani_any_array_index_mut");

        let mut_self_ref = &args[0];
        let expr = self
            .operand_to_expr(mut_self_ref)
            .expect("expecting operand to be a ref to an existing expression");
        // let map = Expr::Field { base: Box::new(expr.clone()), field: String::from("data") };
        let map = Expr::Field { base: Box::new(expr.clone()), field: String::from(".set! ") };

        let index = self.codegen_operand(&args[1]);

        // TODO: change `Stmt::Assignment` to be in terms of a symbol not a
        // string to avoid the hacky code below
        let index_expr = Expr::Select { base: Box::new(map), key: Box::new(index) };
        self.ref_to_expr.insert(assign_to, index_expr);
        Stmt::Skip
    }

    fn operand_to_expr(&self, operand: &Operand<'tcx>) -> Option<&Expr> {
        let Operand::Move(place) = operand else {
            return None;
        };
        self.ref_to_expr.get(place)
    }



}






