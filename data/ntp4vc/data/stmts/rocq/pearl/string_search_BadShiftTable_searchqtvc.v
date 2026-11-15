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
Theorem search'vc (bst : bad_shift_table) (text : string) (fact0 : Z.of_nat (String.length (pat bst)) ≤ Z.of_nat (String.length text)) : let pat1 : string := pat bst in ∀(m : bv 63%N), bv_signed m = Z.of_nat (String.length pat1) ∧ 0%Z ≤ Z.of_nat (String.length pat1) -> (∀(n : bv 63%N), bv_signed n = Z.of_nat (String.length text) ∧ 0%Z ≤ Z.of_nat (String.length text) -> ((0%Z ≤ 0%Z ∧ 0%Z ≤ bv_signed n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < 0%Z -> j ≤ bv_signed n - bv_signed m -> ¬ substring (Z.to_nat j) (Z.to_nat (bv_signed m)) text = pat1)) ∧ (∀(i : bv 63%N), (0%Z ≤ bv_signed i ∧ bv_signed i ≤ bv_signed n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < bv_signed i -> j ≤ bv_signed n - bv_signed m -> ¬ substring (Z.to_nat j) (Z.to_nat (bv_signed m)) text = pat1) -> int'63_in_bounds (bv_signed n - bv_signed m) ∧ (∀(o1 : bv 63%N), bv_signed o1 = bv_signed n - bv_signed m -> (if decide (bv_signed i ≤ bv_signed o1) then (0%Z ≤ bv_signed i ∧ bv_signed i ≤ Z.of_nat (String.length text) - Z.of_nat (String.length pat1)) ∧ (if decide (matches1 pat1 text (bv_signed i)) then (- 1%Z ≤ bv_signed i ∧ bv_signed i ≤ Z.of_nat (String.length text) - Z.of_nat (String.length (pat bst))) ∧ (if decide (bv_signed i = - 1%Z) then ∀(j : Z), ¬ matches1 (pat bst) text j else matches1 (pat bst) text (bv_signed i)) else int'63_in_bounds (bv_signed n - bv_signed m) ∧ (∀(o2 : bv 63%N), bv_signed o2 = bv_signed n - bv_signed m -> (bv_signed i = bv_signed o2 -> i = o2) -> (if decide (i = o2) then (- 1%Z ≤ - 1%Z ∧ - 1%Z ≤ Z.of_nat (String.length text) - Z.of_nat (String.length (pat bst))) ∧ (∀(j : Z), ¬ matches1 (pat bst) text j) else int'63_in_bounds (bv_signed i + bv_signed m) ∧ (∀(o3 : bv 63%N), bv_signed o3 = bv_signed i + bv_signed m -> (0%Z ≤ bv_signed o3 ∧ bv_signed o3 < Z.of_nat (String.length text)) ∧ (let c : ascii := get_str_i text (bv_signed o3) in (if decide (c ∈ dom (to_fmap (sht bst))) then c ∈ dom (to_fmap (sht bst)) else int'63_in_bounds (bv_signed m + 1%Z)) ∧ (∀(o4 : bv 63%N), (if decide (c ∈ dom (to_fmap (sht bst))) then let o5 : t (bv 63%N) := sht bst in o4 = lookup_gmap_total (to_fmap o5) c ∧ o4 = lookup_gmap_total (to_fmap o5) c else bv_signed o4 = bv_signed m + 1%Z) -> int'63_in_bounds (bv_signed i + bv_signed o4) ∧ (∀(o5 : bv 63%N), bv_signed o5 = bv_signed i + bv_signed o4 -> (0%Z ≤ bv_signed n - bv_signed m - bv_signed i ∧ bv_signed n - bv_signed m - bv_signed o5 < bv_signed n - bv_signed m - bv_signed i) ∧ (0%Z ≤ bv_signed o5 ∧ bv_signed o5 ≤ bv_signed n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < bv_signed o5 -> j ≤ bv_signed n - bv_signed m -> ¬ substring (Z.to_nat j) (Z.to_nat (bv_signed m)) text = pat1)))))))) else (- 1%Z ≤ - 1%Z ∧ - 1%Z ≤ Z.of_nat (String.length text) - Z.of_nat (String.length (pat bst))) ∧ (∀(j : Z), ¬ matches1 (pat bst) text j))))).
Admitted.
