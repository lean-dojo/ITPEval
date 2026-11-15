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
Require Import Why3.bintree.Tree.
Require Import Why3.bintree.Size.
Require Import Why3.bintree.Height.
Require Import Why3.bintree.Inorder.
Require Import Why3.bintree.InorderLength.
Open Scope Z_scope.
Axiom elt : Type.
Axiom elt_inhabited : Inhabited elt.
Global Existing Instance elt_inhabited.
Axiom elt_countable : Countable elt.
Global Existing Instance elt_countable.
Theorem tree_of_list'vc (l : list elt) : let o1 : Z := Z.of_nat (length l) in (0%Z ≤ o1 ∧ o1 ≤ Z.of_nat (length l)) ∧ (∀(o2 : tree elt) (o3 : list elt), inorder o2 ++ o3 = l ∧ Size.size o2 = o1 ∧ (0%Z < o1 -> (let h : Z := height o2 in Z.pow 2%Z (h - 1%Z) ≤ o1 ∧ o1 < Z.pow 2%Z h)) -> inorder o2 = l ∧ (0%Z < Size.size o2 -> (let h : Z := height o2 in Z.pow 2%Z (h - 1%Z) ≤ Size.size o2 ∧ Size.size o2 < Z.pow 2%Z h))).
Admitted.
