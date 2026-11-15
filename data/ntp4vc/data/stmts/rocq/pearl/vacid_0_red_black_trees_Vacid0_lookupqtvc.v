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
Require Import vacid_0_red_black_trees_vcg.vacid_0_red_black_trees.RedBlackTree.
Open Scope Z_scope.
Axiom rbt : Type.
Axiom rbt_inhabited : Inhabited rbt.
Global Existing Instance rbt_inhabited.
Axiom rbt_countable : Countable rbt.
Global Existing Instance rbt_countable.
Definition inv (r : Z * tree) := match r with | (_, t) => bst t ∧ (∃(n : Z), rbtree n t) end.
Definition default (r : Z * tree) : Z := match r with | (d, _) => d end.
Definition mem (r : Z * tree) (k : Z) (v : Z) := match r with | (d, t) => memt t k v ∨ v = d ∧ (∀(v' : Z), ¬ memt t k v') end.
Theorem lookup'vc (m : Z) (m1 : tree) (k : Z) (fact0 : inv (m, m1)) : bst m1 ∧ (∀(result : Z), memt m1 k result ∨ (∀(v : Z), ¬ memt m1 k v) ∧ result = m -> mem (m, m1) k result).
Admitted.
