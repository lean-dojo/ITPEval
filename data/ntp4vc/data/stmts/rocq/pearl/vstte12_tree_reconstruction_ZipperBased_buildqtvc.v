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
Program Fixpoint forest_depths (f : list (Z * tree)) : list Z :=
match f with | [] => ([] : list Z) | cons (d, t) r => depths d t ++ forest_depths r end.
Admit Obligations.
Program Fixpoint greedy (d : Z) (d1 : Z) (t1 : tree) : Prop :=
¬ d = d1 ∧ (match t1 with | Leaf => True | Node l1 _ => greedy d (d1 + 1%Z) l1 end).
Admit Obligations.
Inductive g : list (Z * tree) -> Prop :=
 | Gnil : g ([] : list (Z * tree))
 | Gone (d : Z) (t : tree) : g (cons (d, t) ([] : list (Z * tree)))
 | Gtwo (d1 : Z) (d2 : Z) (t2 : tree) (t1 : tree) (l : list (Z * tree)) : greedy d1 d2 t2 -> g (cons (d1, t1) l) -> g (cons (d2, t2) (cons (d1, t1) l)).
Program Fixpoint only_leaf (l : list (Z * tree)) : Prop :=
match l with | [] => True | cons (_, t) r => t = Leaf ∧ only_leaf r end.
Admit Obligations.
Program Fixpoint map_leaf (l : list Z) : list (Z * tree) :=
match l with | [] => ([] : list (Z * tree)) | cons d r => cons (d, Leaf) (map_leaf r) end.
Admit Obligations.
Theorem build'vc (s : list Z) : let o1 : list (Z * tree) := map_leaf s in let o2 : list (Z * tree) := ([] : list (Z * tree)) in (g o2 ∧ (match o1 with | cons (d2, t2) right' => only_leaf right' ∧ (match t2 with | Node l2 _ => g (cons (d2 + 1%Z, l2) o2) | Leaf => True end) | [] => True end)) ∧ (∀(result : tree), depths 0%Z result = forest_depths (rev o2 ++ o1) -> depths 0%Z result = s) ∧ ((∀(t : tree), ¬ depths 0%Z t = forest_depths (rev o2 ++ o1)) -> (∀(t : tree), ¬ depths 0%Z t = s)).
Admitted.
