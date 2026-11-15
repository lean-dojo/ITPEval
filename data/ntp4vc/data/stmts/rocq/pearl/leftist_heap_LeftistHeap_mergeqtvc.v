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
Theorem merge'vc (h1 : tree elt) (h2 : tree elt) (fact0 : leftist_heap h1) (fact1 : leftist_heap h2) : (match h2 with | E => (match h1 with | E => True | _ => True end) | N x x1 x2 x3 => (match h1 with | E => True | N x4 x5 x6 x7 => (if decide (le x6 x2) then ((0%Z ≤ Size.size h1 + Size.size h2 ∧ Size.size x7 + Size.size h2 < Size.size h1 + Size.size h2) ∧ leftist_heap x7 ∧ leftist_heap h2) ∧ (∀(o1 : tree elt), Size.size o1 = Size.size x7 + Size.size h2 ∧ (∀(x8 : elt), occ x8 o1 = occ x8 x7 + occ x8 h2) ∧ leftist_heap o1 -> (leftist_heap o1 ∧ leftist_heap x5) ∧ le_root x6 x5 ∧ le_root x6 o1) else ((0%Z ≤ Size.size h1 + Size.size h2 ∧ Size.size h1 + Size.size x3 < Size.size h1 + Size.size h2) ∧ leftist_heap h1 ∧ leftist_heap x3) ∧ (∀(o1 : tree elt), Size.size o1 = Size.size h1 + Size.size x3 ∧ (∀(x8 : elt), occ x8 o1 = occ x8 h1 + occ x8 x3) ∧ leftist_heap o1 -> (leftist_heap o1 ∧ leftist_heap x1) ∧ le_root x2 x1 ∧ le_root x2 o1)) end) end) ∧ (∀(result : tree elt), (match h2 with | E => (match h1 with | E => result = h1 | _ => result = h1 end) | N x x1 x2 x3 => (match h1 with | E => result = h2 | N x4 x5 x6 x7 => (if decide (le x6 x2) then ∃(o1 : tree elt), (Size.size o1 = Size.size x7 + Size.size h2 ∧ (∀(x8 : elt), occ x8 o1 = occ x8 x7 + occ x8 h2) ∧ leftist_heap o1) ∧ leftist_heap result ∧ minimum result = x6 ∧ Size.size result = 1%Z + Size.size x5 + Size.size o1 ∧ occ x6 result = 1%Z + occ x6 x5 + occ x6 o1 ∧ (∀(y : elt), ¬ x6 = y -> occ y result = occ y x5 + occ y o1) else ∃(o1 : tree elt), (Size.size o1 = Size.size h1 + Size.size x3 ∧ (∀(x8 : elt), occ x8 o1 = occ x8 h1 + occ x8 x3) ∧ leftist_heap o1) ∧ leftist_heap result ∧ minimum result = x2 ∧ Size.size result = 1%Z + Size.size x1 + Size.size o1 ∧ occ x2 result = 1%Z + occ x2 x1 + occ x2 o1 ∧ (∀(y : elt), ¬ x2 = y -> occ y result = occ y x1 + occ y o1)) end) end) -> Size.size result = Size.size h1 + Size.size h2 ∧ (∀(x : elt), occ x result = occ x h1 + occ x h2) ∧ leftist_heap result).
Admitted.
