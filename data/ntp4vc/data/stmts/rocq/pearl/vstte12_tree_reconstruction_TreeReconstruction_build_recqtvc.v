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
Require Import vstte12_tree_reconstruction_vcg.vstte12_tree_reconstruction.Tree.
Open Scope Z_scope.
Theorem build_rec'vc (s : list Z) (d : Z) : match s with | [] => (∀(t : tree) (s' : list Z), ¬ depths d t ++ s' = s) | cons h t => (if decide (h < d) then ∀(t1 : tree) (s' : list Z), ¬ depths d t1 ++ s' = s else if decide (h = d) then s = depths d Leaf ++ t else let o1 : Z := d + 1%Z in (0%Z ≤ hd inhabitant s - d ∧ hd inhabitant s - o1 < hd inhabitant s - d) ∧ (∀(l : tree) (s1 : list Z), s = depths o1 l ++ s1 -> (let o2 : Z := d + 1%Z in (0%Z ≤ Z.of_nat (length s) ∧ Z.of_nat (length s1) < Z.of_nat (length s) ∨ length s = length s1 ∧ 0%Z ≤ hd inhabitant s - d ∧ hd inhabitant s1 - o2 < hd inhabitant s - d) ∧ (∀(r : tree) (s2 : list Z), s1 = depths o2 r ++ s2 -> s = depths d (Node l r) ++ s2) ∧ ((∀(t1 : tree) (s' : list Z), ¬ depths o2 t1 ++ s' = s1) -> (∀(t1 : tree) (s' : list Z), ¬ depths d t1 ++ s' = s)))) ∧ ((∀(t1 : tree) (s' : list Z), ¬ depths o1 t1 ++ s' = s) -> (∀(t1 : tree) (s' : list Z), ¬ depths d t1 ++ s' = s))) end.
Admitted.
