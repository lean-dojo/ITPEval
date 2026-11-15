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
Open Scope Z_scope.
Inductive term :=
  | S : term
  | K : term
  | App : term -> term -> term.
Axiom term_inhabited : Inhabited term.
Global Existing Instance term_inhabited.
Axiom term_countable : Countable term.
Global Existing Instance term_countable.
Program Fixpoint eq (x : term) (y : term) : Prop :=
match (x, y) with | (S, S) => True | (K, K) => True | (App x1 x2, App y1 y2) => eq x1 y1 ∧ eq x2 y2 | (_, _) => False end.
Admit Obligations.
Axiom eq'spec : forall  (x : term) (y : term), eq x y = (x = y).
Program Fixpoint is_value (t : term) : Prop :=
match t with | K => True | S => True | App K v => is_value v | App S v => is_value v | App (App S v1) v2 => is_value v1 ∧ is_value v2 | _ => False end.
Admit Obligations.
Inductive context :=
  | Hole : context
  | Left : context -> term -> context
  | Right : term -> context -> context.
Axiom context_inhabited : Inhabited context.
Global Existing Instance context_inhabited.
Axiom context_countable : Countable context.
Global Existing Instance context_countable.
Program Fixpoint is_context (c : context) : Prop :=
match c with | Hole => True | Left c1 _ => is_context c1 | Right v c1 => is_value v ∧ is_context c1 end.
Admit Obligations.
Program Fixpoint subst (c : context) (t : term) : term :=
match c with | Hole => t | Left c1 t2 => App (subst c1 t) t2 | Right v1 c2 => App v1 (subst c2 t) end.
Admit Obligations.
Inductive infix_mnmngt : term -> term -> Prop :=
 | red_K (c : context) (v1 : term) (v2 : term) : is_context c -> is_value v1 -> is_value v2 -> infix_mnmngt (subst c (App (App K v1) v2)) (subst c v1)
 | red_S (c : context) (v1 : term) (v2 : term) (v3 : term) : is_context c -> is_value v1 -> is_value v2 -> is_value v3 -> infix_mnmngt (subst c (App (App (App S v1) v2) v3)) (subst c (App (App v1 v3) (App v2 v3))).
Inductive relTR : term -> term -> Prop :=
 | BaseTransRefl (x : term) : relTR x x
 | StepTransRefl (x : term) (y : term) (z : term) : relTR x y -> infix_mnmngt y z -> relTR x z.
Axiom relTR_transitive : forall  (x : term) (y : term) (z : term) (fact0 : relTR x y) (fact1 : relTR y z), relTR x z.
Inductive zipper :=
  | ZHole : zipper
  | ZLeft : context -> term -> zipper
  | ZRight : term -> context -> zipper.
Axiom zipper_inhabited : Inhabited zipper.
Global Existing Instance zipper_inhabited.
Axiom zipper_countable : Countable zipper.
Global Existing Instance zipper_countable.
Program Fixpoint subst_c (c : context) (ct : context) : context :=
match c with | Hole => ct | Left c1 t2 => Left (subst_c c1 ct) t2 | Right v1 c2 => Right v1 (subst_c c2 ct) end.
Admit Obligations.
Axiom subst_c'spec : forall  (c : context) (ct : context) (fact0 : is_context c) (fact1 : is_context ct), is_context (subst_c c ct).
Theorem reduction'vc (c : context) (t : term) (fact0 : is_context c) : match t with | S => (let result : term := S in relTR (subst c t) (subst c result) ∧ is_value result) | K => (let result : term := K in relTR (subst c t) (subst c result) ∧ is_value result) | App t1 t2 => (let o1 : context := Left Hole t2 in let o2 : context := subst_c c o1 in (is_context c ∧ is_context o1 -> is_context o2) -> is_context o2 ∧ (∀(v1 : term), relTR (subst o2 t1) (subst o2 v1) ∧ is_value v1 -> (let o3 : context := Right v1 Hole in let o4 : context := subst_c c o3 in (is_context c ∧ is_context o3 -> is_context o4) -> is_context o4 ∧ (∀(v2 : term), relTR (subst o4 t2) (subst o4 v2) ∧ is_value v2 -> (match v1 with | K => (let result : term := App v1 v2 in relTR (subst c t) (subst c result) ∧ is_value result) | S => (let result : term := App v1 v2 in relTR (subst c t) (subst c result) ∧ is_value result) | App S _ => (let result : term := App v1 v2 in relTR (subst c t) (subst c result) ∧ is_value result) | App K v3 => relTR (subst c t) (subst c v3) ∧ is_value v3 | App (App S v3) v4 => is_context c ∧ (∀(result : term), relTR (subst c (App (App v3 v2) (App v4 v2))) (subst c result) ∧ is_value result -> relTR (subst c t) (subst c result) ∧ is_value result) | _ => False end))))) end.
Admitted.
