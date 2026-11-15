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
Axiom key : Type.
Axiom key_inhabited : Inhabited key.
Global Existing Instance key_inhabited.
Axiom key_countable : Countable key.
Global Existing Instance key_countable.
Axiom value : Type.
Axiom value_inhabited : Inhabited value.
Global Existing Instance value_inhabited.
Axiom value_countable : Countable value.
Global Existing Instance value_countable.
Inductive color :=
  | Red : color
  | Black : color.
Axiom color_inhabited : Inhabited color.
Global Existing Instance color_inhabited.
Axiom color_countable : Countable color.
Global Existing Instance color_countable.
Inductive tree :=
  | Leaf : tree
  | Node : color -> tree -> Z -> Z -> tree -> tree.
Axiom tree_inhabited : Inhabited tree.
Global Existing Instance tree_inhabited.
Axiom tree_countable : Countable tree.
Global Existing Instance tree_countable.
Program Fixpoint memt (t : tree) (k : Z) (v : Z) : Prop :=
match t with | Leaf => False | Node _ l k' v' r => k = k' ∧ v = v' ∨ memt l k v ∨ memt r k v end.
Admit Obligations.
Definition lt_tree (x : Z) (t : tree) := ∀(k : Z) (v : Z), memt t k v -> k < x.
Definition gt_tree (x : Z) (t : tree) := ∀(k : Z) (v : Z), memt t k v -> x < k.
Program Fixpoint bst (t : tree) : Prop :=
match t with | Leaf => True | Node _ l k _ r => bst l ∧ bst r ∧ lt_tree k l ∧ gt_tree k r end.
Admit Obligations.
Definition is_not_red (t : tree) := match t with | Node Red _ _ _ _ => False | Leaf => True | Node Black _ _ _ _ => True end.
Program Fixpoint rbtree (n : Z) (t : tree) : Prop :=
match t with | Leaf => n = 0%Z | Node Red l _ _ r => rbtree n l ∧ rbtree n r ∧ is_not_red l ∧ is_not_red r | Node Black l _ _ r => rbtree (n - 1%Z) l ∧ rbtree (n - 1%Z) r end.
Admit Obligations.
Definition almost_rbtree (n : Z) (t : tree) := match t with | Leaf => n = 0%Z | Node Red l _ _ r => rbtree n l ∧ rbtree n r | Node Black l _ _ r => rbtree (n - 1%Z) l ∧ rbtree (n - 1%Z) r end.
Theorem lbalance'vc (k : Z) (l : tree) (r : tree) (v : Z) (fact0 : lt_tree k l) (fact1 : gt_tree k r) (fact2 : bst l) (fact3 : bst r) : (match l with | Node Red (Node Red a kx vx b) ky vy c => True | Node Red a kx vx (Node Red b ky vy c) => True | _ => True end) ∧ (∀(result : tree), (match l with | Node Red (Node Red a kx vx b) ky vy c => result = Node Red (Node Black a kx vx b) ky vy (Node Black c k v r) | Node Red a kx vx (Node Red b ky vy c) => result = Node Red (Node Black a kx vx b) ky vy (Node Black c k v r) | _ => result = Node Black l k v r end) -> bst result ∧ (∀(n : Z), almost_rbtree n l -> rbtree n r -> rbtree (n + 1%Z) result) ∧ (∀(k' : Z) (v' : Z), memt result k' v' = (if decide (k' = k) then v' = v else memt l k' v' ∨ memt r k' v'))).
Admitted.
