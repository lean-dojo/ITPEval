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
Theorem remove'vc (x : key) (h : t) (fact0 : neq x dummy) : let o1 : list key := data h in (neq x dummy ∧ (let n : Z := Z.of_nat (length o1) in 0%Z < n ∧ 0%Z < numof o1 0%Z n)) ∧ (∀(j : Z), (0%Z ≤ j ∧ j < Z.of_nat (length o1)) ∧ (eq (nth (Z.to_nat j) o1 inhabitant) dummy ∨ eq (nth (Z.to_nat j) o1 inhabitant) x) ∧ (∀(j1 : Z), 0%Z ≤ j1 ∧ j1 < Z.of_nat (length o1) -> between (bucket x (Z.of_nat (length o1))) j1 j -> neq (nth (Z.to_nat j1) o1 inhabitant) x ∧ neq (nth (Z.to_nat j1) o1 inhabitant) dummy) -> (let o2 : key := dummy in let o3 : list key := data h in (0%Z ≤ j ∧ j < Z.of_nat (length o3)) ∧ (let o4 : key := nth (Z.to_nat j) o3 inhabitant in neq o4 o2 = (¬ keym1 o4 = keym1 o2) -> (if decide (neq o4 o2) then let o5 : key := dummy in let o6 : list key := data h in (0%Z ≤ j ∧ j < Z.of_nat (length o6)) ∧ (length (set_list o6 (Z.to_nat j) o5) = length o6 -> length (set_list o6 (Z.to_nat j) o5) = length (data h) -> nth_i (set_list o6 (Z.to_nat j) o5) = fun_updt (nth_i o6) j o5 -> (let o7 : Z := next (Z.of_nat (length (data h))) j in ((0%Z ≤ j ∧ j < Z.of_nat (length (set_list o6 (Z.to_nat j) o5))) ∧ (0%Z ≤ o7 ∧ o7 < Z.of_nat (length (set_list o6 (Z.to_nat j) o5))) ∧ ¬ o7 = j ∧ (if decide (j ≤ o7) then 1%Z ≤ numof (set_list o6 (Z.to_nat j) o5) o7 (Z.of_nat (length (set_list o6 (Z.to_nat j) o5))) + numof (set_list o6 (Z.to_nat j) o5) 0%Z j else 1%Z ≤ numof (set_list o6 (Z.to_nat j) o5) o7 j) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (set_list o6 (Z.to_nat j) o5)) -> between j k o7 -> ¬ k = j -> neq (nth (Z.to_nat k) (set_list o6 (Z.to_nat j) o5) inhabitant) dummy)) ∧ (∀(f0 : Z), (0%Z ≤ f0 ∧ f0 < Z.of_nat (length (set_list o6 (Z.to_nat j) o5))) ∧ ¬ f0 = j ∧ eq (nth (Z.to_nat f0) (set_list o6 (Z.to_nat j) o5) inhabitant) dummy ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (set_list o6 (Z.to_nat j) o5)) -> between j k f0 -> ¬ k = j -> neq (nth (Z.to_nat k) (set_list o6 (Z.to_nat j) o5) inhabitant) dummy) -> ((0%Z ≤ f0 ∧ f0 < Z.of_nat (length (set_list o6 (Z.to_nat j) o5))) ∧ (0%Z ≤ j ∧ j < Z.of_nat (length (set_list o6 (Z.to_nat j) o5))) ∧ (0%Z ≤ j ∧ j < Z.of_nat (length (set_list o6 (Z.to_nat j) o5))) ∧ ¬ j = f0 ∧ eq (nth (Z.to_nat j) (set_list o6 (Z.to_nat j) o5) inhabitant) dummy ∧ eq (nth (Z.to_nat f0) (set_list o6 (Z.to_nat j) o5) inhabitant) dummy ∧ between j j f0 ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (set_list o6 (Z.to_nat j) o5)) -> between j k f0 -> ¬ k = j -> neq (nth (Z.to_nat k) (set_list o6 (Z.to_nat j) o5) inhabitant) dummy) ∧ ¬ fun_updt (view h) (keym1 x) false (keym1 dummy) = true ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (set_list o6 (Z.to_nat j) o5)) -> (let x1 : key := nth (Z.to_nat k) (set_list o6 (Z.to_nat j) o5) inhabitant in neq x1 dummy -> fun_updt (view h) (keym1 x) false (keym1 x1) = true ∧ loc h (keym1 x1) = k)) ∧ (let n : Z := Z.of_nat (length (set_list o6 (Z.to_nat j) o5)) in ∀(x1 : key), fun_updt (view h) (keym1 x) false (keym1 x1) = true -> (let k : Z := loc h (keym1 x1) in (0%Z ≤ k ∧ k < n) ∧ eq (nth (Z.to_nat k) (set_list o6 (Z.to_nat j) o5) inhabitant) x1 ∧ (∀(l : Z), 0%Z ≤ l ∧ l < n -> between (bucket x1 n) l k -> neq (nth (Z.to_nat l) (set_list o6 (Z.to_nat j) o5) inhabitant) x1 ∧ (neq (nth (Z.to_nat l) (set_list o6 (Z.to_nat j) o5) inhabitant) dummy ∨ l = j ∧ between j j k))))) ∧ (∀(l : keym -> Z) (h_data : list key), length h_data = length (set_list o6 (Z.to_nat j) o5) -> length h_data = length (set_list o6 (Z.to_nat j) o5) -> numof h_data 0%Z (Z.of_nat (length h_data)) = numof (set_list o6 (Z.to_nat j) o5) 0%Z (Z.of_nat (length h_data)) ∧ valid h_data (fun_updt (view h) (keym1 x) false) l -> (∀(h1 : t), ((0%Z ≤ size h - 1%Z ∧ size h - 1%Z < Z.of_nat (length h_data)) ∧ (let n : Z := Z.of_nat (length h_data) in size h - 1%Z + numof h_data 0%Z n = n) ∧ valid h_data (fun_updt (view h) (keym1 x) false) l) ∧ (l = loc h1 ∧ fun_updt (view h) (keym1 x) false = view h1 ∧ h_data = data h1 ∧ size h - 1%Z = size h1 -> view h1 = fun_updt (view h) (keym1 x) false)))))) else view h = fun_updt (view h) (keym1 x) false)))).
Admitted.
