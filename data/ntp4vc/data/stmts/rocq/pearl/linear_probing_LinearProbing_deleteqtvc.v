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
Theorem delete'vc (f0 : Z) (a : list key) (j : Z) (i : Z) (view1 : keym -> bool) (loc1 : keym -> Z) (fact0 : 0%Z ≤ f0) (fact1 : f0 < Z.of_nat (length a)) (fact2 : 0%Z ≤ j) (fact3 : j < Z.of_nat (length a)) (fact4 : 0%Z ≤ i) (fact5 : i < Z.of_nat (length a)) (fact6 : ¬ j = f0) (fact7 : eq (nth (Z.to_nat j) a inhabitant) dummy) (fact8 : eq (nth (Z.to_nat f0) a inhabitant) dummy) (fact9 : between j i f0) (fact10 : ∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length a) -> between i k f0 -> ¬ k = i -> neq (nth (Z.to_nat k) a inhabitant) dummy) (fact11 : ¬ view1 (keym1 dummy) = true) (fact12 : ∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length a) -> (let x : key := nth (Z.to_nat k) a inhabitant in neq x dummy -> view1 (keym1 x) = true ∧ loc1 (keym1 x) = k)) (fact13 : let n : Z := Z.of_nat (length a) in ∀(x : key), view1 (keym1 x) = true -> (let k : Z := loc1 (keym1 x) in (0%Z ≤ k ∧ k < n) ∧ eq (nth (Z.to_nat k) a inhabitant) x ∧ (∀(l : Z), 0%Z ≤ l ∧ l < n -> between (bucket x n) l k -> neq (nth (Z.to_nat l) a inhabitant) x ∧ (neq (nth (Z.to_nat l) a inhabitant) dummy ∨ l = j ∧ between j i k)))) : let n : Z := Z.of_nat (length a) in let i1 : Z := next n i in (0%Z ≤ i1 ∧ i1 < Z.of_nat (length a)) ∧ (let xi : key := nth (Z.to_nat i1) a inhabitant in let o1 : key := dummy in neq xi o1 = (¬ keym1 xi = keym1 o1) -> (if decide (neq xi o1) then 0%Z < n ∧ (let r : Z := bucket xi n in 0%Z ≤ r ∧ r < n -> (∀(o2 : bool), (if decide (j < r) then o2 = (if decide (r ≤ i1) then true else false) else o2 = false) -> (∀(o3 : bool), (if decide (o2 = true) then o3 = true else ∃(o4 : bool), (if decide (i1 < j) then o4 = (if decide (j < r) then true else false) else o4 = false) ∧ (if decide (o4 = true) then o3 = true else if decide (r ≤ i1) then o3 = (if decide (i1 < j) then true else false) else o3 = false)) -> (if decide (o3 = true) then (0%Z ≤ (if decide (f0 ≤ i) then Z.of_nat (length a) - i + f0 else f0 - i) ∧ (if decide (f0 ≤ i1) then Z.of_nat (length a) - i1 + f0 else f0 - i1) < (if decide (f0 ≤ i) then Z.of_nat (length a) - i + f0 else f0 - i)) ∧ (0%Z ≤ f0 ∧ f0 < Z.of_nat (length a)) ∧ (0%Z ≤ j ∧ j < Z.of_nat (length a)) ∧ (0%Z ≤ i1 ∧ i1 < Z.of_nat (length a)) ∧ ¬ j = f0 ∧ eq (nth (Z.to_nat j) a inhabitant) dummy ∧ eq (nth (Z.to_nat f0) a inhabitant) dummy ∧ between j i1 f0 ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length a) -> between i1 k f0 -> ¬ k = i1 -> neq (nth (Z.to_nat k) a inhabitant) dummy) ∧ ¬ view1 (keym1 dummy) = true ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length a) -> (let x : key := nth (Z.to_nat k) a inhabitant in neq x dummy -> view1 (keym1 x) = true ∧ loc1 (keym1 x) = k)) ∧ (let n1 : Z := Z.of_nat (length a) in ∀(x : key), view1 (keym1 x) = true -> (let k : Z := loc1 (keym1 x) in (0%Z ≤ k ∧ k < n1) ∧ eq (nth (Z.to_nat k) a inhabitant) x ∧ (∀(l : Z), 0%Z ≤ l ∧ l < n1 -> between (bucket x n1) l k -> neq (nth (Z.to_nat l) a inhabitant) x ∧ (neq (nth (Z.to_nat l) a inhabitant) dummy ∨ l = j ∧ between j i1 k)))) else ∀(a1 : list key), length a1 = length a ∧ (∀(i2 : Z), 0%Z ≤ i2 ∧ i2 < Z.of_nat (length a1) -> nth (Z.to_nat i2) a1 inhabitant = nth (Z.to_nat i2) a inhabitant) -> (0%Z ≤ j ∧ j < Z.of_nat (length a)) ∧ (length (set_list a (Z.to_nat j) xi) = length a -> nth_i (set_list a (Z.to_nat j) xi) = fun_updt (nth_i a) j xi -> (∀(a2 : list key), length a2 = length (set_list a (Z.to_nat j) xi) ∧ (∀(i2 : Z), 0%Z ≤ i2 ∧ i2 < Z.of_nat (length a2) -> nth (Z.to_nat i2) a2 inhabitant = nth (Z.to_nat i2) (set_list a (Z.to_nat j) xi) inhabitant) -> (let o4 : key := dummy in (0%Z ≤ i1 ∧ i1 < Z.of_nat (length (set_list a (Z.to_nat j) xi))) ∧ (length (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) = length (set_list a (Z.to_nat j) xi) -> nth_i (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) = fun_updt (nth_i (set_list a (Z.to_nat j) xi)) i1 o4 -> ((0%Z ≤ (if decide (f0 ≤ i) then Z.of_nat (length a) - i + f0 else f0 - i) ∧ (if decide (f0 ≤ i1) then Z.of_nat (length (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4)) - i1 + f0 else f0 - i1) < (if decide (f0 ≤ i) then Z.of_nat (length a) - i + f0 else f0 - i)) ∧ (0%Z ≤ f0 ∧ f0 < Z.of_nat (length (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4))) ∧ (0%Z ≤ i1 ∧ i1 < Z.of_nat (length (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4))) ∧ (0%Z ≤ i1 ∧ i1 < Z.of_nat (length (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4))) ∧ ¬ i1 = f0 ∧ eq (nth (Z.to_nat i1) (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) inhabitant) dummy ∧ eq (nth (Z.to_nat f0) (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) inhabitant) dummy ∧ between i1 i1 f0 ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4)) -> between i1 k f0 -> ¬ k = i1 -> neq (nth (Z.to_nat k) (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) inhabitant) dummy) ∧ ¬ view1 (keym1 dummy) = true ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4)) -> (let x : key := nth (Z.to_nat k) (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) inhabitant in neq x dummy -> view1 (keym1 x) = true ∧ fun_updt loc1 (keym1 xi) j (keym1 x) = k)) ∧ (let n1 : Z := Z.of_nat (length (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4)) in ∀(x : key), view1 (keym1 x) = true -> (let k : Z := fun_updt loc1 (keym1 xi) j (keym1 x) in (0%Z ≤ k ∧ k < n1) ∧ eq (nth (Z.to_nat k) (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) inhabitant) x ∧ (∀(l : Z), 0%Z ≤ l ∧ l < n1 -> between (bucket x n1) l k -> neq (nth (Z.to_nat l) (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) inhabitant) x ∧ (neq (nth (Z.to_nat l) (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) inhabitant) dummy ∨ l = i1 ∧ between i1 i1 k))))) ∧ (∀(loc2 : keym -> Z) (a3 : list key), length a3 = length (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) -> numof a3 0%Z (Z.of_nat (length a3)) = numof (set_list (set_list a (Z.to_nat j) xi) (Z.to_nat i1) o4) 0%Z (Z.of_nat (length a3)) ∧ valid a3 view1 loc2 -> numof a3 0%Z (Z.of_nat (length a3)) = numof a 0%Z (Z.of_nat (length a3)) ∧ valid a3 view1 loc2))))))))) else valid a view1 loc1)).
Admitted.
