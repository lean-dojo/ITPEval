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
Require Import defunctionalization_vcg.defunctionalization.Defunctionalization.
Open Scope Z_scope.
Definition is_a_redex (e : expr) := match e with | Sub (Cte _) (Cte _) => True | _ => False end.
Inductive context :=
  | Empty : context
  | Left : context -> expr -> context
  | Right : Z -> context -> context.
Axiom context_inhabited : Inhabited context.
Global Existing Instance context_inhabited.
Axiom context_countable : Countable context.
Global Existing Instance context_countable.
Program Fixpoint recompose (c : context) (e : expr) : expr :=
match c with | Empty => e | Left c1 e2 => recompose c1 (Sub e e2) | Right n1 c1 => recompose c1 (Sub (Cte n1) e) end.
Admit Obligations.
Definition is_a_value (e : expr) := match e with | Cte _ => True | _ => False end.
Definition is_empty_context (c : context) := match c with | Empty => True | _ => False end.
Program Fixpoint size_c (c : context) : Z :=
match c with | Empty => 0%Z | Left c1 e => 2%Z + size_c c1 + size_e e | Right _ c1 => 1%Z + size_c c1 end.
Admit Obligations.
Theorem eval_1'vc (e : expr) (c : context) : (match e with | Cte n => 0%Z ≤ 2%Z * (size_c c + size_e e) ∧ 1%Z + 2%Z * size_c c < 2%Z * (size_c c + size_e e) | Sub e1 e2 => 0%Z ≤ 2%Z * (size_c c + size_e e) ∧ 2%Z * (size_c (Left c e2) + size_e e1) < 2%Z * (size_c c + size_e e) end) ∧ (∀(result : Z), (match e with | Cte n => result = eval_0 (recompose c (Cte n)) | Sub e1 e2 => result = eval_0 (recompose (Left c e2) e1) end) -> result = eval_0 (recompose c e)).
Admitted.
