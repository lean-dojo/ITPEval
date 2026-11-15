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
Open Scope Z_scope.
Axiom post : Type.
Axiom post_inhabited : Inhabited post.
Global Existing Instance post_inhabited.
Axiom post_countable : Countable post.
Global Existing Instance post_countable.
Inductive hcode :=
  | hcode'mk : list instr -> (state -> state -> bool) -> hcode.
Axiom hcode_inhabited : Inhabited hcode.
Global Existing Instance hcode_inhabited.
Axiom hcode_countable : Countable hcode.
Global Existing Instance hcode_countable.
Definition hcode1 (x : hcode) := match x with |  hcode'mk a _ => a end.
Definition post1 (x : hcode) := match x with |  hcode'mk _ a => a end.
Definition hcode_ok (hc : hcode) := ∀(s : state), post1 hc s (exec_list (hcode1 hc) s) = true.
Axiom trans : Type.
Axiom trans_inhabited : Inhabited trans.
Global Existing Instance trans_inhabited.
Axiom trans_countable : Countable trans.
Global Existing Instance trans_countable.
Inductive wcode :=
  | wcode'mk : ((state -> bool) -> state -> bool) -> list instr -> wcode.
Axiom wcode_inhabited : Inhabited wcode.
Global Existing Instance wcode_inhabited.
Axiom wcode_countable : Countable wcode.
Global Existing Instance wcode_countable.
Definition trans1 (x : wcode) := match x with |  wcode'mk a _ => a end.
Definition wcode1 (x : wcode) := match x with |  wcode'mk _ a => a end.
Definition wcode_ok (wc : wcode) := ∀(q : state -> bool) (s : state), trans1 wc q s = true -> q (exec_list (wcode1 wc) s) = true.
Axiom to_wp : (state -> state -> bool) -> (state -> bool) -> state -> bool.
Axiom to_wp'def : forall  (pst : state -> state -> bool) (q : state -> bool) (s1 : state), (to_wp pst q s1 = true) = (∀(s2 : state), pst s1 s2 = true -> q s2 = true).
Axiom rcompose : forall {β : Type} `{Inhabited β} {γ : Type} `{Inhabited γ} {α : Type} `{Inhabited α}, (α -> β) -> (β -> γ) -> α -> γ.
Axiom rcompose'def : forall  {β : Type} {γ : Type} {α : Type} `{Inhabited β} `{Inhabited γ} `{Inhabited α} (f : α -> β) (g : β -> γ) (x : α), rcompose f g x = g (f x).
Axiom exec_closure : instr -> state -> state.
Axiom exec_closure'def : forall  (i : instr) (s : state), exec_closure i s = exec i s.
Axiom id1 : forall {α : Type} `{Inhabited α}, α -> α.
Axiom id'def : forall  {α : Type} `{Inhabited α} (x : α), id1 x = x.
Theorem wrap'vc (wc : wcode) (pst : state -> state -> bool) (fact0 : wcode_ok wc) (fact1 : ∀(x : state), trans1 wc (pst x) x = true) : hcode_ok (hcode'mk (wcode1 wc) pst).
Admitted.
