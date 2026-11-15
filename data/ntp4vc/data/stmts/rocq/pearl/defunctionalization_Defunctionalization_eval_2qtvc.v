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
Require Import defunctionalization_vcg.defunctionalization.Expr.
Require Import defunctionalization_vcg.defunctionalization.DirectSem.
Open Scope Z_scope.
Inductive cont :=
  | A1 : expr -> cont -> cont
  | A2 : Z -> cont -> cont
  | I : cont.
Axiom cont_inhabited : Inhabited cont.
Global Existing Instance cont_inhabited.
Axiom cont_countable : Countable cont.
Global Existing Instance cont_countable.
Inductive eval_cont : cont -> Z -> Z -> Prop :=
 | a1 (v : Z) (k : cont) (e2 : expr) (r : Z) : eval_cont (A2 v k) (eval_0 e2) r -> eval_cont (A1 e2 k) v r
 | a2 (k : cont) (v1 : Z) (v : Z) (r : Z) : eval_cont k (v1 - v) r -> eval_cont (A2 v1 k) v r
 | a3 (v : Z) : eval_cont I v v.
Program Fixpoint size_e (e : expr) : Z :=
match e with | Cte _ => 1%Z | Sub e1 e2 => 3%Z + size_e e1 + size_e e2 end.
Admit Obligations.
Program Fixpoint size_c (c : cont) : Z :=
match c with | I => 0%Z | A1 e2 k => 2%Z + size_e e2 + size_c k | A2 _ k => 1%Z + size_c k end.
Admit Obligations.
Theorem eval_2'vc (e : expr) (c : cont) : (match e with | Cte n => 0%Z ≤ size_c c + size_e e ∧ size_c c < size_c c + size_e e | Sub e1 e2 => 0%Z ≤ size_c c + size_e e ∧ size_c (A1 e2 c) + size_e e1 < size_c c + size_e e end) ∧ (∀(result : Z), (match e with | Cte n => eval_cont c n result | Sub e1 e2 => eval_cont (A1 e2 c) (eval_0 e1) result end) -> eval_cont c (eval_0 e) result).
Admitted.
