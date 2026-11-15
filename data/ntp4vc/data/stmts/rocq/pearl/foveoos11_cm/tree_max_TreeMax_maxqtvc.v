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
Require Import foveoos11_cm.tree_max.BinTree.
Open Scope Z_scope.
Theorem max'vc (t : tree) (fact0 : ¬ t = Null) : (match t with | Null => False | Tree v l r => True end) ∧ (∀(result : Z), (match t with | Null => False | Tree v l r => (∃(o1 : Z), (ge_tree o1 r ∧ v ≤ o1 ∧ (o1 = v ∨ mem o1 r)) ∧ ge_tree result l ∧ o1 ≤ result ∧ (result = o1 ∨ mem result l)) end) -> ge_tree result t ∧ mem result t).
Admitted.
