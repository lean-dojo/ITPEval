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
Require Import register_allocation_vcg.register_allocation.Spec.
Require Import register_allocation_vcg.register_allocation.DWP.
Open Scope Z_scope.
Axiom identity : (state -> bool) -> state -> bool.
Axiom exec_closure : instr -> state -> state.
Axiom identity_def : forall  (y : state -> bool), identity y = y.
Axiom exec_closure_def : forall  (y : instr) (y1 : state), exec_closure y y1 = exec y y1.
Theorem compile'vc (e : expr) (r : Z) : let o1 : state -> state -> bool := expr_post e r in (match e with | Evar x => (∀(o2 : wcode), wcode_ok o2 ∧ trans1 o2 = identity -> wcode_ok o2) | Eneg e1 => (∀(o2 : wcode), wcode_ok o2 ∧ trans1 o2 = identity -> wcode_ok o2 ∧ (∀(o3 : wcode), wcode_ok o3 ∧ trans1 o3 = rcompose (trans1 o2) (rcompose (exec_closure (Ineg r))) -> (match e with | Evar _ => False | Eneg f => f = e1 | Eadd f f1 => f = e1 ∨ f1 = e1 end) ∧ (∀(o4 : hcode), hcode_ok o4 ∧ post1 o4 = expr_post e1 r -> hcode_ok o4 ∧ (∀(o5 : wcode), wcode_ok o5 ∧ trans1 o5 = to_wp (post1 o4) -> wcode_ok o5 ∧ wcode_ok o3)))) | Eadd e1 e2 => (∀(o2 : wcode), wcode_ok o2 ∧ trans1 o2 = identity -> wcode_ok o2 ∧ (∀(o3 : wcode), wcode_ok o3 ∧ trans1 o3 = rcompose (trans1 o2) (rcompose (exec_closure (Iadd (r + 1%Z) r))) -> (match e with | Evar _ => False | Eneg f => f = e2 | Eadd f f1 => f = e2 ∨ f1 = e2 end) ∧ (∀(o4 : hcode), hcode_ok o4 ∧ post1 o4 = expr_post e2 (r + 1%Z) -> hcode_ok o4 ∧ (∀(o5 : wcode), wcode_ok o5 ∧ trans1 o5 = to_wp (post1 o4) -> (match e with | Evar _ => False | Eneg f => f = e1 | Eadd f f1 => f = e1 ∨ f1 = e1 end) ∧ (∀(o6 : hcode), hcode_ok o6 ∧ post1 o6 = expr_post e1 r -> hcode_ok o6 ∧ (∀(o7 : wcode), wcode_ok o7 ∧ trans1 o7 = to_wp (post1 o6) -> (wcode_ok o7 ∧ wcode_ok o5) ∧ (∀(o8 : wcode), wcode_ok o8 ∧ trans1 o8 = rcompose (trans1 o5) (trans1 o7) -> wcode_ok o8 ∧ wcode_ok o3))))))) end) ∧ (∀(o2 : wcode), (match e with | Evar x => (∃(o3 : wcode), (wcode_ok o3 ∧ trans1 o3 = identity) ∧ wcode_ok o2 ∧ trans1 o2 = rcompose (trans1 o3) (rcompose (exec_closure (Iload x r)))) | Eneg e1 => (∃(o3 : wcode), (wcode_ok o3 ∧ trans1 o3 = identity) ∧ (∃(o4 : wcode), (wcode_ok o4 ∧ trans1 o4 = rcompose (trans1 o3) (rcompose (exec_closure (Ineg r)))) ∧ (∃(o5 : hcode), (hcode_ok o5 ∧ post1 o5 = expr_post e1 r) ∧ (∃(o6 : wcode), (wcode_ok o6 ∧ trans1 o6 = to_wp (post1 o5)) ∧ wcode_ok o2 ∧ trans1 o2 = rcompose (trans1 o4) (trans1 o6))))) | Eadd e1 e2 => (∃(o3 : wcode), (wcode_ok o3 ∧ trans1 o3 = identity) ∧ (∃(o4 : wcode), (wcode_ok o4 ∧ trans1 o4 = rcompose (trans1 o3) (rcompose (exec_closure (Iadd (r + 1%Z) r)))) ∧ (∃(o5 : hcode), (hcode_ok o5 ∧ post1 o5 = expr_post e2 (r + 1%Z)) ∧ (∃(o6 : wcode), (wcode_ok o6 ∧ trans1 o6 = to_wp (post1 o5)) ∧ (∃(o7 : hcode), (hcode_ok o7 ∧ post1 o7 = expr_post e1 r) ∧ (∃(o8 : wcode), (wcode_ok o8 ∧ trans1 o8 = to_wp (post1 o7)) ∧ (∃(o9 : wcode), (wcode_ok o9 ∧ trans1 o9 = rcompose (trans1 o6) (trans1 o8)) ∧ wcode_ok o2 ∧ trans1 o2 = rcompose (trans1 o4) (trans1 o9)))))))) end) -> (wcode_ok o2 ∧ (∀(x : state), trans1 o2 (o1 x) x = true)) ∧ (∀(result : hcode), hcode_ok result ∧ post1 result = o1 -> hcode_ok result ∧ post1 result = expr_post e r)).
Admitted.
