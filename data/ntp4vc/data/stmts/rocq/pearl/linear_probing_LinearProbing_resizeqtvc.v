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
Theorem resize'vc (h : t) : let n : Z := Z.of_nat (length (data h)) in let n2 : Z := 2%Z * n in 0%Z ≤ n2 ∧ (∀(a : list key), (∀(i : Z), 0%Z ≤ i ∧ i < n2 -> nth (Z.to_nat i) a inhabitant = dummy) ∧ Z.of_nat (length a) = n2 -> (let o1 : keym -> Z := (const : Z -> keym -> Z) 0%Z in let o2 : Z := n - 1%Z in (0%Z ≤ o2 + 1%Z -> (numof a 0%Z n2 = numof (data h) 0%Z 0%Z + n2 - 0%Z ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n2 -> neq (nth (Z.to_nat j) a inhabitant) dummy -> view h (keym1 (nth (Z.to_nat j) a inhabitant)) = true ∧ o1 (keym1 (nth (Z.to_nat j) a inhabitant)) = j) ∧ (∀(x : key), view h (keym1 x) = true -> (if decide (loc h (keym1 x) < 0%Z) then let j2 : Z := o1 (keym1 x) in (0%Z ≤ j2 ∧ j2 < n2) ∧ eq (nth (Z.to_nat j2) a inhabitant) x ∧ (∀(k : Z), 0%Z ≤ k ∧ k < n2 -> between (bucket x n2) k j2 -> neq (nth (Z.to_nat k) a inhabitant) x ∧ neq (nth (Z.to_nat k) a inhabitant) dummy) else ∀(j2 : Z), 0%Z ≤ j2 ∧ j2 < n2 -> neq (nth (Z.to_nat j2) a inhabitant) x))) ∧ (∀(l : keym -> Z) (a1 : list key), length a1 = length a -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o2) ∧ numof a1 0%Z n2 = numof (data h) 0%Z i + n2 - i ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n2 -> neq (nth (Z.to_nat j) a1 inhabitant) dummy -> view h (keym1 (nth (Z.to_nat j) a1 inhabitant)) = true ∧ l (keym1 (nth (Z.to_nat j) a1 inhabitant)) = j) ∧ (∀(x : key), view h (keym1 x) = true -> (if decide (loc h (keym1 x) < i) then let j2 : Z := l (keym1 x) in (0%Z ≤ j2 ∧ j2 < n2) ∧ eq (nth (Z.to_nat j2) a1 inhabitant) x ∧ (∀(k : Z), 0%Z ≤ k ∧ k < n2 -> between (bucket x n2) k j2 -> neq (nth (Z.to_nat k) a1 inhabitant) x ∧ neq (nth (Z.to_nat k) a1 inhabitant) dummy) else ∀(j2 : Z), 0%Z ≤ j2 ∧ j2 < n2 -> neq (nth (Z.to_nat j2) a1 inhabitant) x)) -> (let o3 : list key := data h in (0%Z ≤ i ∧ i < Z.of_nat (length o3)) ∧ (let x : key := nth (Z.to_nat i) o3 inhabitant in let o4 : key := dummy in neq x o4 = (¬ keym1 x = keym1 o4) -> (if decide (neq x o4) then (neq x dummy ∧ (let n1 : Z := Z.of_nat (length a1) in 0%Z < n1 ∧ 0%Z < numof a1 0%Z n1)) ∧ (∀(j : Z), (0%Z ≤ j ∧ j < Z.of_nat (length a1)) ∧ (eq (nth (Z.to_nat j) a1 inhabitant) dummy ∨ eq (nth (Z.to_nat j) a1 inhabitant) x) ∧ (∀(j1 : Z), 0%Z ≤ j1 ∧ j1 < Z.of_nat (length a1) -> between (bucket x (Z.of_nat (length a1))) j1 j -> neq (nth (Z.to_nat j1) a1 inhabitant) x ∧ neq (nth (Z.to_nat j1) a1 inhabitant) dummy) -> (0%Z ≤ j ∧ j < Z.of_nat (length a1)) ∧ (length (set_list a1 (Z.to_nat j) x) = length a1 -> nth_i (set_list a1 (Z.to_nat j) x) = fun_updt (nth_i a1) j x -> numof (set_list a1 (Z.to_nat j) x) 0%Z n2 = numof (data h) 0%Z (i + 1%Z) + n2 - (i + 1%Z) ∧ (∀(j1 : Z), 0%Z ≤ j1 ∧ j1 < n2 -> neq (nth (Z.to_nat j1) (set_list a1 (Z.to_nat j) x) inhabitant) dummy -> view h (keym1 (nth (Z.to_nat j1) (set_list a1 (Z.to_nat j) x) inhabitant)) = true ∧ fun_updt l (keym1 x) j (keym1 (nth (Z.to_nat j1) (set_list a1 (Z.to_nat j) x) inhabitant)) = j1) ∧ (∀(x1 : key), view h (keym1 x1) = true -> (if decide (loc h (keym1 x1) < i + 1%Z) then let j2 : Z := fun_updt l (keym1 x) j (keym1 x1) in (0%Z ≤ j2 ∧ j2 < n2) ∧ eq (nth (Z.to_nat j2) (set_list a1 (Z.to_nat j) x) inhabitant) x1 ∧ (∀(k : Z), 0%Z ≤ k ∧ k < n2 -> between (bucket x1 n2) k j2 -> neq (nth (Z.to_nat k) (set_list a1 (Z.to_nat j) x) inhabitant) x1 ∧ neq (nth (Z.to_nat k) (set_list a1 (Z.to_nat j) x) inhabitant) dummy) else ∀(j2 : Z), 0%Z ≤ j2 ∧ j2 < n2 -> neq (nth (Z.to_nat j2) (set_list a1 (Z.to_nat j) x) inhabitant) x1)))) else numof a1 0%Z n2 = numof (data h) 0%Z (i + 1%Z) + n2 - (i + 1%Z) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n2 -> neq (nth (Z.to_nat j) a1 inhabitant) dummy -> view h (keym1 (nth (Z.to_nat j) a1 inhabitant)) = true ∧ l (keym1 (nth (Z.to_nat j) a1 inhabitant)) = j) ∧ (∀(x1 : key), view h (keym1 x1) = true -> (if decide (loc h (keym1 x1) < i + 1%Z) then let j2 : Z := l (keym1 x1) in (0%Z ≤ j2 ∧ j2 < n2) ∧ eq (nth (Z.to_nat j2) a1 inhabitant) x1 ∧ (∀(k : Z), 0%Z ≤ k ∧ k < n2 -> between (bucket x1 n2) k j2 -> neq (nth (Z.to_nat k) a1 inhabitant) x1 ∧ neq (nth (Z.to_nat k) a1 inhabitant) dummy) else ∀(j2 : Z), 0%Z ≤ j2 ∧ j2 < n2 -> neq (nth (Z.to_nat j2) a1 inhabitant) x1)))))) ∧ (numof a1 0%Z n2 = numof (data h) 0%Z (o2 + 1%Z) + n2 - (o2 + 1%Z) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n2 -> neq (nth (Z.to_nat j) a1 inhabitant) dummy -> view h (keym1 (nth (Z.to_nat j) a1 inhabitant)) = true ∧ l (keym1 (nth (Z.to_nat j) a1 inhabitant)) = j) ∧ (∀(x : key), view h (keym1 x) = true -> (if decide (loc h (keym1 x) < o2 + 1%Z) then let j2 : Z := l (keym1 x) in (0%Z ≤ j2 ∧ j2 < n2) ∧ eq (nth (Z.to_nat j2) a1 inhabitant) x ∧ (∀(k : Z), 0%Z ≤ k ∧ k < n2 -> between (bucket x n2) k j2 -> neq (nth (Z.to_nat k) a1 inhabitant) x ∧ neq (nth (Z.to_nat k) a1 inhabitant) dummy) else ∀(j2 : Z), 0%Z ≤ j2 ∧ j2 < n2 -> neq (nth (Z.to_nat j2) a1 inhabitant) x)) -> (∀(h1 : t), ((0%Z ≤ size h ∧ size h < Z.of_nat (length a1)) ∧ (let n3 : Z := Z.of_nat (length a1) in size h + numof a1 0%Z n3 = n3) ∧ valid a1 (view h) l) ∧ (l = loc h1 ∧ view h = view h1 ∧ a1 = data h1 ∧ size h = size h1 -> Z.of_nat (length (data h1)) = 2%Z * Z.of_nat (length (data h))))))) ∧ (o2 + 1%Z < 0%Z -> (∀(h1 : t), ((0%Z ≤ size h ∧ size h < Z.of_nat (length a)) ∧ (let n3 : Z := Z.of_nat (length a) in size h + numof a 0%Z n3 = n3) ∧ valid a (view h) o1) ∧ (o1 = loc h1 ∧ view h = view h1 ∧ a = data h1 ∧ size h = size h1 -> Z.of_nat (length (data h1)) = 2%Z * Z.of_nat (length (data h))))))).
Admitted.
