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
Require Import remove_duplicate_hash_vcg.remove_duplicate_hash.Spec.
Open Scope Z_scope.
Axiom elt : Type.
Axiom elt_inhabited : Inhabited elt.
Global Existing Instance elt_inhabited.
Axiom elt_countable : Countable elt.
Global Existing Instance elt_countable.
Axiom set : Type.
Axiom set_inhabited : Inhabited set.
Global Existing Instance set_inhabited.
Axiom set_countable : Countable set.
Global Existing Instance set_countable.
Axiom to_fset : set -> gset elt.
Axiom choose1 : set -> elt.
Axiom choose'spec : forall  (s : set) (fact0 : ¬ to_fset s = ∅), choose1 s ∈ to_fset s.
Theorem remove_duplicate'vc (a : list elt) (s : set) (fact0 : 1%Z ≤ Z.of_nat (length a)) (fact1 : to_fset s = (∅ : gset elt)) (fact2 : Z.of_nat (size (to_fset s)) = 0%Z) : let o1 : Z := Z.of_nat (length a) - 1%Z in (0%Z ≤ o1 + 1%Z -> (∀(x : elt), appears x a 0%Z = (x ∈ to_fset s)) ∧ (∀(s1 : set), (∀(i : Z), (0%Z ≤ i ∧ i ≤ o1) ∧ (∀(x : elt), appears x a i = (x ∈ to_fset s1)) -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (let o2 : elt := nth (Z.to_nat i) a inhabitant in ∀(s2 : set), to_fset s2 = insert_set o2 (to_fset s1) ∧ (if decide (o2 ∈ to_fset s1) then size (to_fset s2) = size (to_fset s1) else Z.of_nat (size (to_fset s2)) = Z.of_nat (size (to_fset s1)) + 1%Z) -> (∀(x : elt), appears x a (i + 1%Z) = (x ∈ to_fset s2)))) ∧ ((∀(x : elt), appears x a (o1 + 1%Z) = (x ∈ to_fset s1)) -> (0%Z ≤ 0%Z ∧ 0%Z < Z.of_nat (length a)) ∧ (let o2 : Z := Z.of_nat (size (to_fset s1)) in 0%Z ≤ o2 ∧ (∀(r : list elt), (∀(i : Z), 0%Z ≤ i ∧ i < o2 -> nth (Z.to_nat i) r inhabitant = nth 0%nat a inhabitant) ∧ Z.of_nat (length r) = o2 -> (∀(s2 : set), to_fset s2 = (∅ : gset elt) -> (let o3 : Z := Z.of_nat (length a) - 1%Z in (0%Z ≤ o3 + 1%Z -> ((∀(x : elt), appears x a 0%Z = (x ∈ to_fset s2)) ∧ (∀(x : elt), (x ∈ to_fset s2) = appears x r 0%Z) ∧ nodup r 0%Z ∧ (0%Z ≤ 0%Z ∧ 0%Z = Z.of_nat (size (to_fset s2)) ∧ Z.of_nat (size (to_fset s2)) ≤ Z.of_nat (length r)) ∧ to_fset s2 ⊆ to_fset s1) ∧ (∀(j : Z) (r1 : list elt) (s3 : set), length r1 = length r -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o3) ∧ (∀(x : elt), appears x a i = (x ∈ to_fset s3)) ∧ (∀(x : elt), (x ∈ to_fset s3) = appears x r1 j) ∧ nodup r1 j ∧ (0%Z ≤ j ∧ j = Z.of_nat (size (to_fset s3)) ∧ Z.of_nat (size (to_fset s3)) ≤ Z.of_nat (length r1)) ∧ to_fset s3 ⊆ to_fset s1 -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (if decide (¬ nth (Z.to_nat i) a inhabitant ∈ to_fset s3) then (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (let o4 : elt := nth (Z.to_nat i) a inhabitant in ∀(s4 : set), to_fset s4 = insert_set o4 (to_fset s3) ∧ (if decide (o4 ∈ to_fset s3) then size (to_fset s4) = size (to_fset s3) else Z.of_nat (size (to_fset s4)) = Z.of_nat (size (to_fset s3)) + 1%Z) -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (let o5 : elt := nth (Z.to_nat i) a inhabitant in (0%Z ≤ j ∧ j < Z.of_nat (length r1)) ∧ (length (set_list r1 (Z.to_nat j) o5) = length r1 -> nth_i (set_list r1 (Z.to_nat j) o5) = fun_updt (nth_i r1) j o5 -> (∀(x : elt), appears x a (i + 1%Z) = (x ∈ to_fset s4)) ∧ (∀(x : elt), (x ∈ to_fset s4) = appears x (set_list r1 (Z.to_nat j) o5) (j + 1%Z)) ∧ nodup (set_list r1 (Z.to_nat j) o5) (j + 1%Z) ∧ (0%Z ≤ j + 1%Z ∧ j + 1%Z = Z.of_nat (size (to_fset s4)) ∧ Z.of_nat (size (to_fset s4)) ≤ Z.of_nat (length (set_list r1 (Z.to_nat j) o5))) ∧ to_fset s4 ⊆ to_fset s1))) else (∀(x : elt), appears x a (i + 1%Z) = (x ∈ to_fset s3)) ∧ (∀(x : elt), (x ∈ to_fset s3) = appears x r1 j) ∧ nodup r1 j ∧ (0%Z ≤ j ∧ j = Z.of_nat (size (to_fset s3)) ∧ Z.of_nat (size (to_fset s3)) ≤ Z.of_nat (length r1)) ∧ to_fset s3 ⊆ to_fset s1)) ∧ ((∀(x : elt), appears x a (o3 + 1%Z) = (x ∈ to_fset s3)) ∧ (∀(x : elt), (x ∈ to_fset s3) = appears x r1 j) ∧ nodup r1 j ∧ (0%Z ≤ j ∧ j = Z.of_nat (size (to_fset s3)) ∧ Z.of_nat (size (to_fset s3)) ≤ Z.of_nat (length r1)) ∧ to_fset s3 ⊆ to_fset s1 -> nodup r1 (Z.of_nat (length r1)) ∧ (∀(x : elt), appears x a (Z.of_nat (length a)) = appears x r1 (Z.of_nat (length r1)))))) ∧ (o3 + 1%Z < 0%Z -> nodup r (Z.of_nat (length r)) ∧ (∀(x : elt), appears x a (Z.of_nat (length a)) = appears x r (Z.of_nat (length r))))))))))) ∧ (o1 + 1%Z < 0%Z -> (0%Z ≤ 0%Z ∧ 0%Z < Z.of_nat (length a)) ∧ (let o2 : Z := Z.of_nat (size (to_fset s)) in 0%Z ≤ o2 ∧ (∀(r : list elt), (∀(i : Z), 0%Z ≤ i ∧ i < o2 -> nth (Z.to_nat i) r inhabitant = nth 0%nat a inhabitant) ∧ Z.of_nat (length r) = o2 -> (∀(s1 : set), to_fset s1 = (∅ : gset elt) -> (let o3 : Z := Z.of_nat (length a) - 1%Z in (0%Z ≤ o3 + 1%Z -> ((∀(x : elt), appears x a 0%Z = (x ∈ to_fset s1)) ∧ (∀(x : elt), (x ∈ to_fset s1) = appears x r 0%Z) ∧ nodup r 0%Z ∧ (0%Z ≤ 0%Z ∧ 0%Z = Z.of_nat (size (to_fset s1)) ∧ Z.of_nat (size (to_fset s1)) ≤ Z.of_nat (length r)) ∧ to_fset s1 ⊆ to_fset s) ∧ (∀(j : Z) (r1 : list elt) (s2 : set), length r1 = length r -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o3) ∧ (∀(x : elt), appears x a i = (x ∈ to_fset s2)) ∧ (∀(x : elt), (x ∈ to_fset s2) = appears x r1 j) ∧ nodup r1 j ∧ (0%Z ≤ j ∧ j = Z.of_nat (size (to_fset s2)) ∧ Z.of_nat (size (to_fset s2)) ≤ Z.of_nat (length r1)) ∧ to_fset s2 ⊆ to_fset s -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (if decide (¬ nth (Z.to_nat i) a inhabitant ∈ to_fset s2) then (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (let o4 : elt := nth (Z.to_nat i) a inhabitant in ∀(s3 : set), to_fset s3 = insert_set o4 (to_fset s2) ∧ (if decide (o4 ∈ to_fset s2) then size (to_fset s3) = size (to_fset s2) else Z.of_nat (size (to_fset s3)) = Z.of_nat (size (to_fset s2)) + 1%Z) -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (let o5 : elt := nth (Z.to_nat i) a inhabitant in (0%Z ≤ j ∧ j < Z.of_nat (length r1)) ∧ (length (set_list r1 (Z.to_nat j) o5) = length r1 -> nth_i (set_list r1 (Z.to_nat j) o5) = fun_updt (nth_i r1) j o5 -> (∀(x : elt), appears x a (i + 1%Z) = (x ∈ to_fset s3)) ∧ (∀(x : elt), (x ∈ to_fset s3) = appears x (set_list r1 (Z.to_nat j) o5) (j + 1%Z)) ∧ nodup (set_list r1 (Z.to_nat j) o5) (j + 1%Z) ∧ (0%Z ≤ j + 1%Z ∧ j + 1%Z = Z.of_nat (size (to_fset s3)) ∧ Z.of_nat (size (to_fset s3)) ≤ Z.of_nat (length (set_list r1 (Z.to_nat j) o5))) ∧ to_fset s3 ⊆ to_fset s))) else (∀(x : elt), appears x a (i + 1%Z) = (x ∈ to_fset s2)) ∧ (∀(x : elt), (x ∈ to_fset s2) = appears x r1 j) ∧ nodup r1 j ∧ (0%Z ≤ j ∧ j = Z.of_nat (size (to_fset s2)) ∧ Z.of_nat (size (to_fset s2)) ≤ Z.of_nat (length r1)) ∧ to_fset s2 ⊆ to_fset s)) ∧ ((∀(x : elt), appears x a (o3 + 1%Z) = (x ∈ to_fset s2)) ∧ (∀(x : elt), (x ∈ to_fset s2) = appears x r1 j) ∧ nodup r1 j ∧ (0%Z ≤ j ∧ j = Z.of_nat (size (to_fset s2)) ∧ Z.of_nat (size (to_fset s2)) ≤ Z.of_nat (length r1)) ∧ to_fset s2 ⊆ to_fset s -> nodup r1 (Z.of_nat (length r1)) ∧ (∀(x : elt), appears x a (Z.of_nat (length a)) = appears x r1 (Z.of_nat (length r1)))))) ∧ (o3 + 1%Z < 0%Z -> nodup r (Z.of_nat (length r)) ∧ (∀(x : elt), appears x a (Z.of_nat (length a)) = appears x r (Z.of_nat (length r))))))))).
Admitted.
