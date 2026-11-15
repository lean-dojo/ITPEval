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
Require Import string_search_vcg.string_search.Spec.
Require Import string_search_vcg.string_search.Occurs.
Require Import Why3.ocaml.Exceptions.
Open Scope Z_scope.
Axiom t : Type -> Type.
Axiom t_inhabited : forall  {χ : Type} `{Inhabited χ} `{Countable χ}, Inhabited (t χ).
Global Existing Instance t_inhabited.
Axiom to_fmap : forall {χ : Type} `{Inhabited χ} `{Countable χ}, t χ -> gmap ascii χ.
Axiom bad_shift_table : Type.
Axiom bad_shift_table_inhabited : Inhabited bad_shift_table.
Global Existing Instance bad_shift_table_inhabited.
Axiom bad_shift_table_countable : Countable bad_shift_table.
Global Existing Instance bad_shift_table_countable.
Axiom pat : bad_shift_table -> string.
Axiom sht : bad_shift_table -> t (bv 63%N).
Axiom bad_shift_table'invariant : forall  (self : bad_shift_table), (∀(j : Z) (c : ascii), 0%Z ≤ j ∧ j < Z.of_nat (String.length (pat self)) -> c = get_str_i (pat self) j -> c ∈ dom (to_fmap (sht self))) ∧ (∀(c : ascii), c ∈ dom (to_fmap (sht self)) -> 1%Z ≤ bv_signed (lookup_gmap_total (to_fmap (sht self)) c) ∧ bv_signed (lookup_gmap_total (to_fmap (sht self)) c) ≤ Z.of_nat (String.length (pat self)) + 1%Z) ∧ (∀(c : ascii), c ∈ dom (to_fmap (sht self)) -> (∀(j : Z), 1%Z ≤ j ∧ j < bv_signed (lookup_gmap_total (to_fmap (sht self)) c) -> ¬ get_str_i (pat self) (Z.of_nat (String.length (pat self)) - j) = c)).
Definition bad_shift_table'eq (a : bad_shift_table) (b : bad_shift_table) := pat a = pat b ∧ sht a = sht b.
Axiom bad_shift_table'inj : forall  (a : bad_shift_table) (b : bad_shift_table) (fact0 : bad_shift_table'eq a b), a = b.
Theorem make_table'vc (m : bv 63%N) (pat1 : string) (sht1 : t (bv 63%N)) (fact0 : bv_signed m = Z.of_nat (String.length pat1)) (fact1 : 0%Z ≤ Z.of_nat (String.length pat1)) (fact2 : to_fmap sht1 = (∅ : gmap ascii (bv 63%N))) : int'63_in_bounds (bv_signed m - 1%Z) ∧ (∀(o1 : bv 63%N), bv_signed o1 = bv_signed m - 1%Z -> (0%Z ≤ bv_signed o1 + 1%Z -> ((∀(j : Z), 0%Z ≤ j ∧ j < 0%Z -> get_str_i pat1 j ∈ dom (to_fmap sht1)) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht1) -> 1%Z ≤ bv_signed (lookup_gmap_total (to_fmap sht1) c) ∧ bv_signed (lookup_gmap_total (to_fmap sht1) c) ≤ bv_signed m + 1%Z) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht1) -> (∀(j : Z), bv_signed m - bv_signed (lookup_gmap_total (to_fmap sht1) c) < j ∧ j < 0%Z -> ¬ get_str_i pat1 j = c))) ∧ (∀(sht2 : t (bv 63%N)), (∀(i : bv 63%N), let i1 : Z := bv_signed i in (0%Z ≤ i1 ∧ i1 ≤ bv_signed o1) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i1 -> get_str_i pat1 j ∈ dom (to_fmap sht2)) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht2) -> 1%Z ≤ bv_signed (lookup_gmap_total (to_fmap sht2) c) ∧ bv_signed (lookup_gmap_total (to_fmap sht2) c) ≤ bv_signed m + 1%Z) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht2) -> (∀(j : Z), bv_signed m - bv_signed (lookup_gmap_total (to_fmap sht2) c) < j ∧ j < i1 -> ¬ get_str_i pat1 j = c)) -> int'63_in_bounds (bv_signed m - bv_signed i) ∧ (∀(o2 : bv 63%N), bv_signed o2 = bv_signed m - bv_signed i -> (0%Z ≤ bv_signed i ∧ bv_signed i < Z.of_nat (String.length pat1)) ∧ (∀(sht3 : t (bv 63%N)), to_fmap sht3 = <[get_str_i pat1 (bv_signed i) := o2]>(to_fmap sht2) -> (∀(j : Z), 0%Z ≤ j ∧ j < i1 + 1%Z -> get_str_i pat1 j ∈ dom (to_fmap sht3)) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht3) -> 1%Z ≤ bv_signed (lookup_gmap_total (to_fmap sht3) c) ∧ bv_signed (lookup_gmap_total (to_fmap sht3) c) ≤ bv_signed m + 1%Z) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht3) -> (∀(j : Z), bv_signed m - bv_signed (lookup_gmap_total (to_fmap sht3) c) < j ∧ j < i1 + 1%Z -> ¬ get_str_i pat1 j = c))))) ∧ ((∀(j : Z), 0%Z ≤ j ∧ j < bv_signed o1 + 1%Z -> get_str_i pat1 j ∈ dom (to_fmap sht2)) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht2) -> 1%Z ≤ bv_signed (lookup_gmap_total (to_fmap sht2) c) ∧ bv_signed (lookup_gmap_total (to_fmap sht2) c) ≤ bv_signed m + 1%Z) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht2) -> (∀(j : Z), bv_signed m - bv_signed (lookup_gmap_total (to_fmap sht2) c) < j ∧ j < bv_signed o1 + 1%Z -> ¬ get_str_i pat1 j = c)) -> (∀(j : Z), 0%Z ≤ j ∧ j < Z.of_nat (String.length pat1) -> get_str_i pat1 j ∈ dom (to_fmap sht2)) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht2) -> 1%Z ≤ bv_signed (lookup_gmap_total (to_fmap sht2) c) ∧ bv_signed (lookup_gmap_total (to_fmap sht2) c) ≤ Z.of_nat (String.length pat1) + 1%Z) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht2) -> (∀(j : Z), 1%Z ≤ j ∧ j < bv_signed (lookup_gmap_total (to_fmap sht2) c) -> ¬ get_str_i pat1 (Z.of_nat (String.length pat1) - j) = c))))) ∧ (bv_signed o1 + 1%Z < 0%Z -> (∀(j : Z), 0%Z ≤ j ∧ j < Z.of_nat (String.length pat1) -> get_str_i pat1 j ∈ dom (to_fmap sht1)) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht1) -> 1%Z ≤ bv_signed (lookup_gmap_total (to_fmap sht1) c) ∧ bv_signed (lookup_gmap_total (to_fmap sht1) c) ≤ Z.of_nat (String.length pat1) + 1%Z) ∧ (∀(c : ascii), c ∈ dom (to_fmap sht1) -> (∀(j : Z), 1%Z ≤ j ∧ j < bv_signed (lookup_gmap_total (to_fmap sht1) c) -> ¬ get_str_i pat1 (Z.of_nat (String.length pat1) - j) = c)))).
Admitted.
