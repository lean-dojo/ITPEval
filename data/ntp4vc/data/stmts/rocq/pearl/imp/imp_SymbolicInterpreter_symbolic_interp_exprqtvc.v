From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import imp.imp.Syntax.
Require Import imp.imp.ConcreteSemantics.
Require Import imp.imp.Svar.
Require Import imp.imp.Constraint.
Require Import imp.imp.SymState.
Require Import imp.imp.FreshSvar.
Require Import imp.imp.SymStateSet.
Open Scope Z_scope.
Axiom compose : (svar -> Z) -> t -> program_var -> option Z.
Axiom compose'def : forall  (rho : svar -> Z) (sigma : t) (x : program_var), compose rho sigma x = (match get sigma x with | Some v => Some (rho v) | None => None end).
Theorem symbolic_interp_expr'vc (e : expr) (s : sym_state) : match e with | Elit n => (let result : symbolic_expr := Slit n in eval_expr (compose (SymState.rho s) (sigma s)) e (Enormal (interp_symbolic_expr (SymState.rho s) result)) ∧ (∀(v : svar), v ∈ vars_in_symbolic_expr result -> (∃(x : program_var), get (sigma s) x = Some v))) | Evar x => (∀(o1 : svar), get (sigma s) x = Some o1 -> (let result : symbolic_expr := Svar o1 in eval_expr (compose (SymState.rho s) (sigma s)) e (Enormal (interp_symbolic_expr (SymState.rho s) result)) ∧ (∀(v : svar), v ∈ vars_in_symbolic_expr result -> (∃(x1 : program_var), get (sigma s) x1 = Some v)))) ∧ (get (sigma s) x = None -> eval_expr (compose (SymState.rho s) (sigma s)) e Eunbound_var) | Esub e1 e2 => (match e with | Elit _ => False | Evar _ => False | Esub f f1 => f = e2 ∨ f1 = e2 end) ∧ (∀(o1 : symbolic_expr), eval_expr (compose (SymState.rho s) (sigma s)) e2 (Enormal (interp_symbolic_expr (SymState.rho s) o1)) ∧ (∀(v : svar), v ∈ vars_in_symbolic_expr o1 -> (∃(x : program_var), get (sigma s) x = Some v)) -> (match e with | Elit _ => False | Evar _ => False | Esub f f1 => f = e1 ∨ f1 = e1 end) ∧ (∀(o2 : symbolic_expr), eval_expr (compose (SymState.rho s) (sigma s)) e1 (Enormal (interp_symbolic_expr (SymState.rho s) o2)) ∧ (∀(v : svar), v ∈ vars_in_symbolic_expr o2 -> (∃(x : program_var), get (sigma s) x = Some v)) -> (let result : symbolic_expr := Ssub o2 o1 in eval_expr (compose (SymState.rho s) (sigma s)) e (Enormal (interp_symbolic_expr (SymState.rho s) result)) ∧ (∀(v : svar), v ∈ vars_in_symbolic_expr result -> (∃(x : program_var), get (sigma s) x = Some v)))) ∧ (eval_expr (compose (SymState.rho s) (sigma s)) e1 Eunbound_var -> eval_expr (compose (SymState.rho s) (sigma s)) e Eunbound_var)) ∧ (eval_expr (compose (SymState.rho s) (sigma s)) e2 Eunbound_var -> eval_expr (compose (SymState.rho s) (sigma s)) e Eunbound_var) end.
Admitted.
