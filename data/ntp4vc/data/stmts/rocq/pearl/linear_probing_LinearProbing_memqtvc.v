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
Require Import Why3.int.NumOf.
Require Import Why3.map.Const.
Open Scope Z_scope.
Axiom key : Type.
Axiom key_inhabited : Inhabited key.
Global Existing Instance key_inhabited.
Axiom key_countable : Countable key.
Global Existing Instance key_countable.
Axiom keym : Type.
Axiom keym_inhabited : Inhabited keym.
Global Existing Instance keym_inhabited.
Axiom keym_countable : Countable keym.
Global Existing Instance keym_countable.
Axiom keym1 : key -> keym.
Axiom eq : key -> key -> Prop.
Axiom eq'spec : forall  (x : key) (y : key), eq x y = (keym1 x = keym1 y).
Definition neq (x : key) (y : key) := ¬ eq x y.
Axiom neq'spec : forall  (x : key) (y : key), neq x y = (¬ keym1 x = keym1 y).
Axiom hash : key -> Z.
Axiom hash_nonneg : forall  (k : key), 0%Z ≤ hash k.
Axiom hash_eq : forall  (x : key) (y : key) (fact0 : eq x y), hash x = hash y.
Axiom dummy : key.
Axiom bucket : key -> Z -> Z.
Axiom bucket'def : forall  (n : Z) (k : key) (fact0 : 0%Z < n), bucket k n = Z.quot (hash k) n.
Axiom bucket'spec : forall  (n : Z) (k : key) (fact0 : 0%Z < n), 0%Z ≤ bucket k n ∧ bucket k n < n.
Definition between (l : Z) (j : Z) (r : Z) := l ≤ j ∧ j < r ∨ r < l ∧ l ≤ j ∨ j < r ∧ r < l.
Axiom fc : list key -> Z -> bool.
Axiom fc'def : forall  (a : list key) (i : Z), (fc a i = true) = eq (nth (Z.to_nat i) a inhabitant) dummy.
Definition numof (a : list key) (l : Z) (u : Z) : Z := NumOf.numof (fc a) l u.
Definition valid (data : list key) (view : keym -> bool) (loc : keym -> Z) := ¬ view (keym1 dummy) = true ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length data) -> (let x : key := nth (Z.to_nat i) data inhabitant in neq x dummy -> view (keym1 x) = true ∧ loc (keym1 x) = i)) ∧ (let n : Z := Z.of_nat (length data) in ∀(x : key), view (keym1 x) = true -> (let i : Z := loc (keym1 x) in (0%Z ≤ i ∧ i < n) ∧ eq (nth (Z.to_nat i) data inhabitant) x ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n -> between (bucket x n) j i -> neq (nth (Z.to_nat j) data inhabitant) x ∧ neq (nth (Z.to_nat j) data inhabitant) dummy))).
Axiom t : Type.
Axiom t_inhabited : Inhabited t.
Global Existing Instance t_inhabited.
Axiom t_countable : Countable t.
Global Existing Instance t_countable.
Axiom size : t -> Z.
Axiom data : t -> list key.
Axiom view : t -> keym -> bool.
Axiom loc : t -> keym -> Z.
Axiom t'invariant : forall  (self : t), 0%Z ≤ size self ∧ size self < Z.of_nat (length (data self)) ∧ size self + numof (data self) 0%Z (Z.of_nat (length (data self))) = Z.of_nat (length (data self)) ∧ valid (data self) (view self) (loc self).
Definition t'eq (a : t) (b : t) := size a = size b ∧ data a = data b ∧ view a = view b ∧ loc a = loc b.
Axiom t'inj : forall  (a : t) (b : t) (fact0 : t'eq a b), a = b.
Definition next (n : Z) (i : Z) : Z := let i1 : Z := i + 1%Z in if decide (i1 = n) then 0%Z else i1.
Theorem mem'vc (x : key) (h : t) (fact0 : neq x dummy) : let o1 : key := dummy in let o2 : list key := data h in (neq x dummy ∧ (let n : Z := Z.of_nat (length o2) in 0%Z < n ∧ 0%Z < numof o2 0%Z n)) ∧ (∀(o3 : Z), (0%Z ≤ o3 ∧ o3 < Z.of_nat (length o2)) ∧ (eq (nth (Z.to_nat o3) o2 inhabitant) dummy ∨ eq (nth (Z.to_nat o3) o2 inhabitant) x) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < Z.of_nat (length o2) -> between (bucket x (Z.of_nat (length o2))) j o3 -> neq (nth (Z.to_nat j) o2 inhabitant) x ∧ neq (nth (Z.to_nat j) o2 inhabitant) dummy) -> (let o4 : list key := data h in (0%Z ≤ o3 ∧ o3 < Z.of_nat (length o4)) ∧ (let o5 : key := nth (Z.to_nat o3) o4 inhabitant in neq o5 o1 = (¬ keym1 o5 = keym1 o1) -> neq o5 o1 = (view h (keym1 x) = true)))).
Admitted.
