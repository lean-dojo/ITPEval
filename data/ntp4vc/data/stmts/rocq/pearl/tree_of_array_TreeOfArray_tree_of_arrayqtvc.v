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
Open Scope Z_scope.
Theorem tree_of_array'vc {α : Type} `{Inhabited α} (a : list α) : let o1 : Z := Z.of_nat (length a) in (0%Z ≤ 0%Z ∧ 0%Z ≤ o1 ∧ o1 ≤ Z.of_nat (length a)) ∧ (∀(result : tree α), (let n : Z := o1 - 0%Z in Size.size result = n ∧ inorder result = drop 0%nat (take (Z.to_nat o1 - 0%nat) a) ∧ (0%Z < n -> (let h : Z := height result in Z.pow 2%Z (h - 1%Z) ≤ n ∧ n < Z.pow 2%Z h))) -> inorder result = drop 0%nat (take (length a - 0%nat) a) ∧ (0%Z < Size.size result -> (let h : Z := height result in Z.pow 2%Z (h - 1%Z) ≤ Size.size result ∧ Size.size result < Z.pow 2%Z h))).
Admitted.
