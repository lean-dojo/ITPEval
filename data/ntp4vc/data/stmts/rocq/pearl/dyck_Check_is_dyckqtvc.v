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
Require Import Why3.why3.Ref.Ref.
Require Import dyck_vcg.dyck.Dyck.
Open Scope Z_scope.
Definition fall (p : list paren) (s : list paren) := dyck p ∧ (match s with | cons L _ => False | _ => True end).
Theorem is_dyck'vc (w : list paren) (o2 : list paren) : (∀(o1 : list paren), w = o2 ++ o1 ∧ fall o2 o1 ∧ (∀(p2 : list paren) (s : list paren), w = p2 ++ s ∧ fall p2 s -> p2 = o2 ∧ s = o1) -> (∀(result : bool), (match o1 with | [] => result = true | _ => result = false end) -> (result = true) = dyck w)) ∧ ((∀(p : list paren) (s : list paren), w = p ++ s -> ¬ fall p s) -> ¬ dyck w).
Admitted.
