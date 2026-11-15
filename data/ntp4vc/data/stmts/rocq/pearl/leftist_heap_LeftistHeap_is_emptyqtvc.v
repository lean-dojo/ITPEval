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
Require Import leftist_heap_vcg.leftist_heap.TreeRank.
Require Import leftist_heap_vcg.leftist_heap.Size.
Require Import leftist_heap_vcg.leftist_heap.Occ.
Open Scope Z_scope.
Axiom elt : Type.
Axiom elt_inhabited : Inhabited elt.
Global Existing Instance elt_inhabited.
Axiom elt_countable : Countable elt.
Global Existing Instance elt_countable.
Axiom le : elt -> elt -> Prop.
Axiom Refl : forall  (x : elt), le x x.
Axiom Trans : forall  (x : elt) (y : elt) (z : elt) (fact0 : le x y) (fact1 : le y z), le x z.
Axiom Total : forall  (x : elt) (y : elt), le x y ∨ le y x.
Axiom t : Type.
Axiom t_inhabited : Inhabited t.
Global Existing Instance t_inhabited.
Axiom t_countable : Countable t.
Global Existing Instance t_countable.
Definition le_root (e : elt) (h : tree elt) := match h with | E => True | N _ _ x _ => le e x end.
Program Fixpoint is_heap (h : tree elt) : Prop :=
match h with | E => True | N _ l x r => le_root x l ∧ is_heap l ∧ le_root x r ∧ is_heap r end.
Admit Obligations.
Axiom minimum : tree elt -> elt.
Axiom minimum_def : forall  (s : Z) (l : tree elt) (x : elt) (r : tree elt), minimum (N s l x r) = x.
Definition is_minimum (x : elt) (h : tree elt) := mem x h ∧ (∀(e : elt), mem e h -> le x e).
Program Fixpoint rank (h : tree elt) : Z :=
match h with | E => 0%Z | N _ l _ r => 1%Z + Z.min (rank l) (rank r) end.
Admit Obligations.
Program Fixpoint leftist (h : tree elt) : Prop :=
match h with | E => True | N s l _ r => s = rank h ∧ leftist l ∧ leftist r ∧ rank r ≤ rank l end.
Admit Obligations.
Definition leftist_heap (h : tree elt) := is_heap h ∧ leftist h.
Theorem is_empty'vc (h : tree elt) (result : bool) (fact0 : match h with | E => result = true | N _ _ _ _ => result = false end) : (result = true) = (Size.size h = 0%Z).
Admitted.
