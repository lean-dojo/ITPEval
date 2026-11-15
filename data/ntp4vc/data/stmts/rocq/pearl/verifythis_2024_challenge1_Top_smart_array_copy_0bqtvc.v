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
Definition permutation (l : Z) (p : list Z) := (0%Z ≤ l ∧ l ≤ Z.of_nat (length p)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < l -> 0%Z ≤ nth (Z.to_nat i) p inhabitant ∧ nth (Z.to_nat i) p inhabitant < l) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < l -> 0%Z ≤ j ∧ j < l -> ¬ i = j -> ¬ nth (Z.to_nat i) p inhabitant = nth (Z.to_nat j) p inhabitant).
Definition permutation_pair (l : Z) (p : list Z) (invp : list Z) := permutation l p ∧ permutation l invp ∧ (∀(i : Z), 0%Z ≤ i ∧ i < l -> nth (Z.to_nat (nth (Z.to_nat i) invp inhabitant)) p inhabitant = i) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < l -> nth (Z.to_nat (nth (Z.to_nat i) p inhabitant)) invp inhabitant = i).
Axiom identity : Z -> list Z.
Axiom identity'spec'1 : forall  (l : Z) (fact0 : 0%Z < l), Z.of_nat (length (identity l)) = l.
Axiom identity'spec'0 : forall  (l : Z) (i : Z) (fact0 : 0%Z < l) (fact1 : 0%Z ≤ i) (fact2 : i < l), nth (Z.to_nat i) (identity l) inhabitant = i.
Axiom identity'spec : forall  (l : Z) (fact0 : 0%Z < l), permutation_pair l (identity l) (identity l).
Axiom elt : Type.
Axiom elt_inhabited : Inhabited elt.
Global Existing Instance elt_inhabited.
Axiom elt_countable : Countable elt.
Global Existing Instance elt_countable.
Definition valid_chunk (a : list elt) (ofs : Z) (len : Z) := 0%Z ≤ ofs ∧ ofs ≤ ofs + len ∧ ofs + len ≤ Z.of_nat (length a).
Definition copy (src : list elt) (dst : list elt) (ofs : Z) (len : Z) := valid_chunk src ofs len ∧ length src = length dst ∧ (∀(i : Z), ofs ≤ i ∧ i < ofs + len -> nth (Z.to_nat i) dst inhabitant = nth (Z.to_nat i) src inhabitant).
Definition copy_to (src : list elt) (dst : list elt) (ofss : Z) (ofsd : Z) (len : Z) := valid_chunk src ofss len ∧ valid_chunk dst ofsd len ∧ length src = length dst ∧ (∀(i : Z), 0%Z ≤ i ∧ i < len -> nth (Z.to_nat (ofsd + i)) dst inhabitant = nth (Z.to_nat (ofss + i)) src inhabitant) ∧ (∀(i : Z), ofsd ≤ i ∧ i < ofsd + len -> nth (Z.to_nat i) dst inhabitant = nth (Z.to_nat (i + (ofss - ofsd))) src inhabitant).
Theorem smart_array_copy_0b'vc (src : list elt) (dst : list elt) (k : Z) (l : Z) (q : Z) (r : Z) (fact0 : length src = length dst) (fact1 : 0%Z < Z.of_nat (length dst)) (fact2 : 0%Z < k) (fact3 : 0%Z < l) (fact4 : 0%Z ≤ q) (fact5 : 0%Z ≤ r) (fact6 : r < k * l) (fact7 : Z.of_nat (length dst) = q * k * l + r) : let m : Z := k * l in let o1 : Z := q - 1%Z in (0%Z ≤ o1 + 1%Z -> copy src dst 0%Z (0%Z * m) ∧ (∀(dst1 : list elt), length dst1 = length dst -> (∀(s : Z), (0%Z ≤ s ∧ s ≤ o1) ∧ copy src dst1 0%Z (s * m) -> (let start : Z := s * m in 0%Z < l ∧ (∀(sigma : list Z) (invsigma : list Z), (length sigma = length invsigma ∧ Z.of_nat (length invsigma) = l) ∧ permutation_pair l sigma invsigma -> (let o2 : Z := l - 1%Z in (0%Z ≤ o2 + 1%Z -> (copy src dst1 0%Z (s * m) ∧ (∀(j' : Z), 0%Z ≤ j' ∧ j' < 0%Z -> copy src dst1 (start + nth (Z.to_nat j') sigma inhabitant * k) k)) ∧ (∀(dst2 : list elt), length dst2 = length dst1 -> (∀(j : Z), (0%Z ≤ j ∧ j ≤ o2) ∧ copy src dst2 0%Z (s * m) ∧ (∀(j' : Z), 0%Z ≤ j' ∧ j' < j -> copy src dst2 (start + nth (Z.to_nat j') sigma inhabitant * k) k) -> (0%Z ≤ j ∧ j < Z.of_nat (length sigma)) ∧ (let startj : Z := start + nth (Z.to_nat j) sigma inhabitant * k in (length src = length dst2 ∧ valid_chunk src startj k ∧ valid_chunk dst2 startj k) ∧ (∀(dst3 : list elt), length dst3 = length dst2 -> copy_to src dst3 startj startj k ∧ (∀(i : Z), 0%Z ≤ i ∧ i < startj -> nth (Z.to_nat i) dst3 inhabitant = nth (Z.to_nat i) dst2 inhabitant) ∧ (∀(i : Z), startj + k ≤ i ∧ i < Z.of_nat (length dst3) -> nth (Z.to_nat i) dst3 inhabitant = nth (Z.to_nat i) dst2 inhabitant) -> copy src dst3 0%Z (s * m) ∧ (∀(j' : Z), 0%Z ≤ j' ∧ j' < j + 1%Z -> copy src dst3 (start + nth (Z.to_nat j') sigma inhabitant * k) k)))) ∧ (copy src dst2 0%Z (s * m) ∧ (∀(j' : Z), 0%Z ≤ j' ∧ j' < o2 + 1%Z -> copy src dst2 (start + nth (Z.to_nat j') sigma inhabitant * k) k) -> copy src dst2 0%Z ((s + 1%Z) * m)))) ∧ (o2 + 1%Z < 0%Z -> copy src dst1 0%Z ((s + 1%Z) * m)))))) ∧ (copy src dst1 0%Z ((o1 + 1%Z) * m) -> (let last : Z := q * m in (length src = length dst1 ∧ valid_chunk src last r ∧ valid_chunk dst1 last r) ∧ (∀(dst2 : list elt), length dst2 = length dst1 -> copy_to src dst2 last last r ∧ (∀(i : Z), 0%Z ≤ i ∧ i < last -> nth (Z.to_nat i) dst2 inhabitant = nth (Z.to_nat i) dst1 inhabitant) ∧ (∀(i : Z), last + r ≤ i ∧ i < Z.of_nat (length dst2) -> nth (Z.to_nat i) dst2 inhabitant = nth (Z.to_nat i) dst1 inhabitant) -> copy src dst2 0%Z (Z.of_nat (length dst))))))) ∧ (o1 + 1%Z < 0%Z -> (let last : Z := q * m in (length src = length dst ∧ valid_chunk src last r ∧ valid_chunk dst last r) ∧ (∀(dst1 : list elt), length dst1 = length dst -> copy_to src dst1 last last r ∧ (∀(i : Z), 0%Z ≤ i ∧ i < last -> nth (Z.to_nat i) dst1 inhabitant = nth (Z.to_nat i) dst inhabitant) ∧ (∀(i : Z), last + r ≤ i ∧ i < Z.of_nat (length dst1) -> nth (Z.to_nat i) dst1 inhabitant = nth (Z.to_nat i) dst inhabitant) -> copy src dst1 0%Z (Z.of_nat (length dst))))).
Admitted.
