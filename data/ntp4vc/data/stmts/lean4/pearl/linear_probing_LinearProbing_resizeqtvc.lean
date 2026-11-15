import Mathlib

open Classical

namespace Lean4Why3

instance {n : Nat} : HShiftLeft (BitVec n) Int (BitVec n) where
  hShiftLeft x k := x <<< k.toNat

instance {n : Nat} : HShiftRight (BitVec n) Int (BitVec n) where
  hShiftRight x k := x >>> k.toNat

abbrev sshiftRight'i {n : ℕ} (a : BitVec n) (s : Int) : BitVec n := a.sshiftRight s.toNat

abbrev make_str_i (size : Int) := String.mk (List.replicate (Int.toNat size) 'a')
abbrev _root_.List.create_i {α} (n : ℤ) (f : ℤ -> α) := (List.range n.toNat).map f
abbrev _root_.List.create {α} (n : ℕ) (f : ℕ -> α) := (List.range n).map f

abbrev _root_.Bool.imp (a b : Bool) : Bool := !a || b

abbrev _root_.List.replicate_i {α} (n : ℤ) (x : α) := List.replicate (Int.toNat n) x

abbrev take_i {α : Type} (n : ℤ) (l : List α) := List.take n.toNat l
abbrev drop_i {α : Type} (n : ℤ) (l : List α) := List.drop n.toNat l

abbrev getElem_i! {α : Type} [Inhabited α] (l : List α) (i : Int) := l[i.toNat]!
abbrev getElem_i? {α : Type} (l : List α) (i : Int) := l[i.toNat]?

abbrev length_i {α : Type} (l : List α) := Int.ofNat l.length
abbrev slice {α : Type} (l : List α) (i j : Nat) : List α :=
  (l.drop i).take (j - i)
abbrev slice_i {α : Type} (l : List α) (i j : Int) : List α :=
  (l.drop i.toNat).take (j.toNat - i.toNat)

abbrev Sorted {α : Type} [LE α] (l : List α) := List.Sorted LE.le l
abbrev _root_.List.set_i {α : Type} (l : List α) (n : ℤ) (a : α) :=
  List.set l n.toNat a

abbrev implication (P : Prop) (Q : Prop) := P -> Q

noncomputable def map_occ {α : Type} (v : α) (m : Int -> α) (l u : Int)
  := {n | l ≤ n ∧ n < u ∧ m n = v }.ncard
noncomputable abbrev map_occ_i {α : Type} (v : α) (m : Int -> α) (l u : Int)
  := Int.ofNat (map_occ (v : α) (m : Int -> α) (l : Int) u)

abbrev _root_.BitVec.toUInt {n : Nat} (x : BitVec n) := Int.ofNat x.toNat

abbrev int'16_max : BitVec 16 := 32767
abbrev int'16_min : BitVec 16 := -32768
abbrev int'31_max : BitVec 31 := 1073741823
abbrev int'31_min : BitVec 31 := -1073741824
abbrev int'32_max : BitVec 32 := 2147483647
abbrev int'32_min : BitVec 32 := -2147483648
abbrev int'63_max : BitVec 63 := 4611686018427387903
abbrev int'63_min : BitVec 63 := -4611686018427387904
abbrev int'64_max : BitVec 64 := 9223372036854775807
abbrev int'64_min : BitVec 64 := -9223372036854775808
abbrev uint'16_max : BitVec 16 := 65535
abbrev uint'16_min : BitVec 16 := 0
abbrev uint'31_max : BitVec 31 := 2147483647
abbrev uint'31_min : BitVec 31 := 0
abbrev uint'32_max : BitVec 32 := 4294967295
abbrev uint'32_min : BitVec 32 := 0
abbrev uint'63_max : BitVec 63 := 9223372036854775807
abbrev uint'63_min : BitVec 63 := 0
abbrev uint'64_max : BitVec 64 := 18446744073709551615
abbrev uint'64_min : BitVec 64 := 0

abbrev int'16_in_bounds (x : Int) := int'16_min.toInt ≤ x ∧ x ≤ int'16_max.toInt
abbrev int'31_in_bounds (x : Int) := int'31_min.toInt ≤ x ∧ x ≤ int'31_max.toInt
abbrev int'32_in_bounds (x : Int) := int'32_min.toInt ≤ x ∧ x ≤ int'32_max.toInt
abbrev int'63_in_bounds (x : Int) := int'63_min.toInt ≤ x ∧ x ≤ int'63_max.toInt
abbrev int'64_in_bounds (x : Int) := int'64_min.toInt ≤ x ∧ x ≤ int'64_max.toInt
abbrev uint'8_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ 256
abbrev uint'16_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ int'16_max.toUInt
abbrev uint'31_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ int'31_max.toUInt
abbrev uint'32_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ int'32_max.toUInt
abbrev uint'63_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ int'63_max.toUInt
abbrev uint'64_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ int'64_max.toUInt

axiom array31 : Type -> Type
axiom array32 : Type -> Type
axiom array63 : Type -> Type

axiom array31_elts : {α : Type} -> array31 α -> Int -> α
axiom array32_elts : {α : Type} -> array32 α -> Int -> α
axiom array63_elts : {α : Type} -> array63 α -> List α

noncomputable abbrev array63_nth {α : Type} [Inhabited α] (a : array63 α) (i : Int) := (array63_elts a)[i.toNat]!

axiom array31_length : {α : Type} -> array31 α -> BitVec 31
axiom array32_length : {α : Type} -> array32 α -> BitVec 32
axiom array63_length : {α : Type} -> array63 α -> BitVec 63

abbrev is_none {α : Type} (x : Option α) := x = none
abbrev is_nil {α : Type} (x : List α) := x = []

abbrev _root_.List.rev_append {α : Type} (a : List α) (b : List α) := a.reverse ++ b
abbrev _root_.Finset.is_empty {α : Type} (s : Finset α) := s = ∅
abbrev _root_.Finset.filter' {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] : Finset α
  := Finset.filter p s

abbrev _root_.Finset.card_i {α : Type} (s : Finset α) := Int.ofNat s.card

abbrev int_power (x : Int) (n : Int) := x ^ n.toNat
abbrev bv2_power (n : Int) := Int.ofNat (2 ^ n.toNat)

abbrev take_bit_i {n : Nat} (x : BitVec n) (i : Int) := x[i.toNat]!
abbrev take_bit_bv {n m : Nat} (x : BitVec n) (i : BitVec m) := x[i.toNat]!

noncomputable def _root_.Finset.pick! {α} [Inhabited α] (s : Finset α) : α :=
  if h : s.Nonempty then Classical.choose h else default
noncomputable def _root_.Set.pick! {α} [Inhabited α] (s : Finset α) : α :=
  if h : s.Nonempty then Classical.choose h else default

noncomputable abbrev _root_.BitVec.eq_sub {m : Nat} (a b : BitVec m) (i n : Nat) :=
  BitVec.extractLsb (i+n-1) i a = BitVec.extractLsb (i+n-1) i b

noncomputable abbrev _root_.BitVec.eq_sub_i {m : Nat} (a b : BitVec m) (i n : Int) :=
  BitVec.eq_sub a b i.toNat n.toNat

noncomputable abbrev _root_.BitVec.eq_sub_bv {m : Nat} {m1 : Nat} {m2 : Nat} (a b : BitVec m) (i : BitVec m1) (n : BitVec m2) :=
  BitVec.eq_sub a b i.toNat n.toNat

abbrev w8_size_bv := (8 : BitVec 8)
abbrev w16_size_bv := (16 : BitVec 16)
abbrev w32_size_bv := (32 : BitVec 32)
abbrev w64_size_bv := (64 : BitVec 64)
abbrev w128_size_bv := (128 : BitVec 128)
abbrev w256_size_bv := (256 : BitVec 256)
abbrev w8_size_i := (8 : Int)
abbrev w16_size_i := (16 : Int)
abbrev w32_size_i := (32 : Int)
abbrev w64_size_i := (64 : Int)
abbrev w128_size_i := (128 : Int)
abbrev w256_size_i := (256 : Int)

abbrev _root_.Finset.erase' {α : Type} [DecidableEq α] (a : α) (s : Finset α) : Finset α
  := Finset.erase s a

abbrev _root_.BitVec.sge {n : ℕ} (x y : BitVec n) := BitVec.sle y x
abbrev _root_.BitVec.sgt {n : ℕ} (x y : BitVec n) := BitVec.slt y x

abbrev _root_.BitVec.sshiftRight_i {n : ℕ} (x : BitVec n) (s : ℤ) := BitVec.sshiftRight x s.toNat
abbrev _root_.BitVec.sshiftRight_bv {n m : ℕ} (x : BitVec n) (s : BitVec m)
  := BitVec.sshiftRight x s.toNat

abbrev _root_.BitVec.rotateLeft_i {w : ℕ} (x : BitVec w) (n : ℤ) := BitVec.rotateLeft x n.toNat
abbrev _root_.BitVec.rotateLeft_nv {w w2 : ℕ} (x : BitVec w) (n : BitVec w2)
  := BitVec.rotateLeft x n.toNat

abbrev _root_.BitVec.rotateRight_i {w : ℕ} (x : BitVec w) (n : ℤ) := BitVec.rotateRight x n.toNat
abbrev _root_.BitVec.rotateRight_nv {w w2 : ℕ} (x : BitVec w) (n : BitVec w2)
  := BitVec.rotateRight x n.toNat

abbrev _root_.Multiset.count_i {α : Type} [DecidableEq α] (a : α) (s : Multiset α)
  := Int.ofNat (s.count a)

abbrev _root_.Multiset.card_i {α : Type} (S : Multiset α) := Int.ofNat S.card

abbrev _root_.Int.gcd_i (a : ℤ) (b : ℤ) := Int.ofNat (Int.gcd a b)

abbrev _root_.Int.Prime (p : ℤ) := Nat.Prime p.toNat
abbrev _root_.Int.Coprime (a b : ℤ) := Nat.Coprime a.toNat b.toNat

abbrev _root_.Set.remove {α : Type} (x : α) (A : Set α) := A \ {x}
abbrev _root_.Set.filter {α : Type} (S : Set α) (P : α -> Bool) := {x ∈ S | P x }

abbrev _root_.Option.the {α : Type} [Inhabited α] (opt : Option α) := opt.getD default

noncomputable abbrev _root_.Finmap.lookup! {K : Type} {V : Type} [Inhabited V] (m : Finmap (fun _ : K => V)) (k : K) :=
  (Finmap.lookup k m).getD default

noncomputable abbrev _root_.Finmap.mapsto {K V : Type} (k : K) (v : V) (m : Finmap (fun _ : K => V))
  := Finmap.lookup k m = some v

abbrev _root_.Finmap.is_empty {K V : Type} (m : Finmap (fun _ : K => V)) := m = ∅
abbrev _root_.Finmap.size {K V : Type} (m : Finmap (fun _ : K => V)) := m.keys.card

abbrev _root_.Finset.min'' {α} [Inhabited α] [LinearOrder α] (s : Finset α) : α :=
  match s.min with
  | ⊤        => default
  | .some a  => a

abbrev _root_.Finset.max'' {α} [Inhabited α] [LinearOrder α] (s : Finset α) : α :=
  match s.max with
  | ⊥        => default
  | .some a  => a

abbrev arrayExchange {α} [Inhabited α] (a1 a2 : List α) (i j : Int) : Prop :=
  let i' := i.toNat
  let j' := j.toNat
  a1 = (a2.set i' a1[j']!).set j' (a1[i']!)

abbrev _root_.List.permut_sub {α} (a1 a2 : List α) (l u : ℕ) : Prop :=
  a1.length = a2.length ∧ (0 ≤ l ∧ l ≤ a1.length) ∧ (0 ≤ u ∧ u ≤ a1.length) ∧
  List.Perm (slice a1 l u) (slice a2 l u)

abbrev _root_.List.permut_sub' {α} (a1 a2 : List α) (l u : ℕ) : Prop :=
  a1.length = a2.length ∧ slice a1 0 l = slice a2 0 l ∧
  slice a1 u a1.length = slice a2 u a1.length ∧
  List.Perm (slice a1 l u) (slice a2 l u)

abbrev _root_.List.foldr' {α β} (f : α -> β -> β) (l : List α) (x : β) := List.foldr f x l

abbrev _root_.Int.to_Real (z : ℤ) : ℝ := z

abbrev _root_.List.mem' {α} (eq : α -> α -> Bool) (x : α) (l : List α) := List.all l (eq x)

noncomputable abbrev _root_.Real.truncate (x : ℝ) : ℤ := if 0 ≤ x then Int.floor x  else Int.ceil x

alias _root_.Math.abs := abs

end Lean4Why3

open Classical
open Lean4Why3

namespace Ref
structure ref (α : Type) where
  contents : α
axiom inhabited_axiom_ref {α : Type} [Inhabited α] : Inhabited (ref α)
attribute [instance] inhabited_axiom_ref
end Ref
namespace NumOf
axiom numof : (ℤ -> Bool) -> ℤ -> ℤ -> ℤ
axiom numof'def (b : ℤ) (a : ℤ) (p : ℤ -> Bool) : if b ≤ a then numof p a b = (0 : ℤ) else if p (b - (1 : ℤ)) = true then numof p a b = (1 : ℤ) + numof p a (b - (1 : ℤ)) else numof p a b = numof p a (b - (1 : ℤ))
axiom Numof_bounds (a : ℤ) (b : ℤ) (p : ℤ -> Bool) (fact0 : a < b) : (0 : ℤ) ≤ numof p a b ∧ numof p a b ≤ b - a
axiom Numof_append (a : ℤ) (b : ℤ) (c : ℤ) (p : ℤ -> Bool) (fact0 : a ≤ b) (fact1 : b ≤ c) : numof p a c = numof p a b + numof p b c
axiom Numof_left_no_add (a : ℤ) (b : ℤ) (p : ℤ -> Bool) (fact0 : a < b) (fact1 : ¬p a = true) : numof p a b = numof p (a + (1 : ℤ)) b
axiom Numof_left_add (a : ℤ) (b : ℤ) (p : ℤ -> Bool) (fact0 : a < b) (fact1 : p a = true) : numof p a b = (1 : ℤ) + numof p (a + (1 : ℤ)) b
axiom Empty (a : ℤ) (b : ℤ) (p : ℤ -> Bool) (fact0 : ∀(n : ℤ), a ≤ n ∧ n < b → ¬p n = true) : numof p a b = (0 : ℤ)
axiom Full (a : ℤ) (b : ℤ) (p : ℤ -> Bool) (fact0 : a ≤ b) (fact1 : ∀(n : ℤ), a ≤ n ∧ n < b → p n = true) : numof p a b = b - a
axiom numof_increasing (i : ℤ) (j : ℤ) (k : ℤ) (p : ℤ -> Bool) (fact0 : i ≤ j) (fact1 : j ≤ k) : numof p i j ≤ numof p i k
axiom numof_strictly_increasing (i : ℤ) (j : ℤ) (k : ℤ) (l : ℤ) (p : ℤ -> Bool) (fact0 : i ≤ j) (fact1 : j ≤ k) (fact2 : k < l) (fact3 : p k = true) : numof p i j < numof p i l
axiom numof_change_any (a : ℤ) (b : ℤ) (p1 : ℤ -> Bool) (p2 : ℤ -> Bool) (fact0 : ∀(j : ℤ), a ≤ j ∧ j < b → p1 j = true → p2 j = true) : numof p1 a b ≤ numof p2 a b
axiom numof_change_some (a : ℤ) (i : ℤ) (b : ℤ) (p1 : ℤ -> Bool) (p2 : ℤ -> Bool) (fact0 : a ≤ i) (fact1 : i < b) (fact2 : ∀(j : ℤ), a ≤ j ∧ j < b → p1 j = true → p2 j = true) (fact3 : ¬p1 i = true) (fact4 : p2 i = true) : numof p1 a b < numof p2 a b
axiom numof_change_equiv (a : ℤ) (b : ℤ) (p1 : ℤ -> Bool) (p2 : ℤ -> Bool) (fact0 : ∀(j : ℤ), a ≤ j ∧ j < b → (p1 j = true) = (p2 j = true)) : numof p2 a b = numof p1 a b
end NumOf
namespace Const
axiom const :  {β : Type} -> [Inhabited β] ->  {α : Type} -> [Inhabited α] -> β -> α -> β
axiom const'def {β : Type} {α : Type} [Inhabited β] [Inhabited α] (v : β) (x : α) : (const : β -> α -> β) v x = v
end Const
namespace linear_probing_LinearProbing_resizeqtvc
axiom key : Type
axiom inhabited_axiom_key : Inhabited key
attribute [instance] inhabited_axiom_key
axiom keym : Type
axiom inhabited_axiom_keym : Inhabited keym
attribute [instance] inhabited_axiom_keym
axiom keym1 : key -> keym
axiom eq : key -> key -> Prop
axiom eq'spec (x : key) (y : key) : eq x y = (keym1 x = keym1 y)
noncomputable def neq (x : key) (y : key) := ¬eq x y
axiom neq'spec (x : key) (y : key) : neq x y = (¬keym1 x = keym1 y)
axiom hash : key -> ℤ
axiom hash_nonneg (k : key) : (0 : ℤ) ≤ hash k
axiom hash_eq (x : key) (y : key) (fact0 : eq x y) : hash x = hash y
axiom dummy : key
axiom bucket : key -> ℤ -> ℤ
axiom bucket'def (n : ℤ) (k : key) (fact0 : (0 : ℤ) < n) : bucket k n = Int.tmod (hash k) n
axiom bucket'spec (n : ℤ) (k : key) (fact0 : (0 : ℤ) < n) : (0 : ℤ) ≤ bucket k n ∧ bucket k n < n
noncomputable def between (l : ℤ) (j : ℤ) (r : ℤ) := l ≤ j ∧ j < r ∨ r < l ∧ l ≤ j ∨ j < r ∧ r < l
axiom fc : List key -> ℤ -> Bool
axiom fc'def (a : List key) (i : ℤ) : (fc a i = true) = eq (a[Int.toNat i]!) dummy
noncomputable def numof (a : List key) (l : ℤ) (u : ℤ) := NumOf.numof (fc a) l u
noncomputable def valid (data : List key) (view : keym -> Bool) (loc : keym -> ℤ) := ¬view (keym1 dummy) = true ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length data) → (let x : key := data[Int.toNat i]!; neq x dummy → view (keym1 x) = true ∧ loc (keym1 x) = i)) ∧ (let n : ℤ := Int.ofNat (List.length data); ∀(x : key), view (keym1 x) = true → (let i : ℤ := loc (keym1 x); ((0 : ℤ) ≤ i ∧ i < n) ∧ eq (data[Int.toNat i]!) x ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < n → between (bucket x n) j i → neq (data[Int.toNat j]!) x ∧ neq (data[Int.toNat j]!) dummy)))
axiom t : Type
axiom inhabited_axiom_t : Inhabited t
attribute [instance] inhabited_axiom_t
axiom size : t -> ℤ
axiom data : t -> List key
axiom view : t -> keym -> Bool
axiom loc : t -> keym -> ℤ
axiom t'invariant (self : t) : (0 : ℤ) ≤ size self ∧ size self < Int.ofNat (List.length (data self)) ∧ size self + numof (data self) (0 : ℤ) (Int.ofNat (List.length (data self))) = Int.ofNat (List.length (data self)) ∧ valid (data self) (view self) (loc self)
noncomputable def t'eq (a : t) (b : t) := size a = size b ∧ data a = data b ∧ view a = view b ∧ loc a = loc b
axiom t'inj (a : t) (b : t) (fact0 : t'eq a b) : a = b
noncomputable def next (n : ℤ) (i : ℤ) := let i1 : ℤ := i + (1 : ℤ); if i1 = n then (0 : ℤ) else i1
theorem resize'vc (h : t) : let n : ℤ := Int.ofNat (List.length (data h)); let n2 : ℤ := (2 : ℤ) * n; (0 : ℤ) ≤ n2 ∧ (∀(a : List key), (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n2 → a[Int.toNat i]! = dummy) ∧ Int.ofNat (List.length a) = n2 → (let o1 : keym -> ℤ := Const.const (0 : ℤ); let o2 : ℤ := n - (1 : ℤ); ((0 : ℤ) ≤ o2 + (1 : ℤ) → (numof a (0 : ℤ) n2 = numof (data h) (0 : ℤ) (0 : ℤ) + n2 - (0 : ℤ) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < n2 → neq (a[Int.toNat j]!) dummy → view h (keym1 (a[Int.toNat j]!)) = true ∧ o1 (keym1 (a[Int.toNat j]!)) = j) ∧ (∀(x : key), view h (keym1 x) = true → (if loc h (keym1 x) < (0 : ℤ) then let j2 : ℤ := o1 (keym1 x); ((0 : ℤ) ≤ j2 ∧ j2 < n2) ∧ eq (a[Int.toNat j2]!) x ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < n2 → between (bucket x n2) k j2 → neq (a[Int.toNat k]!) x ∧ neq (a[Int.toNat k]!) dummy) else ∀(j2 : ℤ), (0 : ℤ) ≤ j2 ∧ j2 < n2 → neq (a[Int.toNat j2]!) x))) ∧ (∀(l : keym -> ℤ) (a1 : List key), List.length a1 = List.length a → (∀(i : ℤ), ((0 : ℤ) ≤ i ∧ i ≤ o2) ∧ numof a1 (0 : ℤ) n2 = numof (data h) (0 : ℤ) i + n2 - i ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < n2 → neq (a1[Int.toNat j]!) dummy → view h (keym1 (a1[Int.toNat j]!)) = true ∧ l (keym1 (a1[Int.toNat j]!)) = j) ∧ (∀(x : key), view h (keym1 x) = true → (if loc h (keym1 x) < i then let j2 : ℤ := l (keym1 x); ((0 : ℤ) ≤ j2 ∧ j2 < n2) ∧ eq (a1[Int.toNat j2]!) x ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < n2 → between (bucket x n2) k j2 → neq (a1[Int.toNat k]!) x ∧ neq (a1[Int.toNat k]!) dummy) else ∀(j2 : ℤ), (0 : ℤ) ≤ j2 ∧ j2 < n2 → neq (a1[Int.toNat j2]!) x)) → (let o3 : List key := data h; ((0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3)) ∧ (let x : key := o3[Int.toNat i]!; let o4 : key := dummy; neq x o4 = (¬keym1 x = keym1 o4) → (if neq x o4 then (neq x dummy ∧ (let n1 : ℤ := Int.ofNat (List.length a1); (0 : ℤ) < n1 ∧ (0 : ℤ) < numof a1 (0 : ℤ) n1)) ∧ (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length a1)) ∧ (eq (a1[Int.toNat j]!) dummy ∨ eq (a1[Int.toNat j]!) x) ∧ (∀(j1 : ℤ), (0 : ℤ) ≤ j1 ∧ j1 < Int.ofNat (List.length a1) → between (bucket x (Int.ofNat (List.length a1))) j1 j → neq (a1[Int.toNat j1]!) x ∧ neq (a1[Int.toNat j1]!) dummy) → ((0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length a1)) ∧ (List.length (List.set a1 (Int.toNat j) x) = List.length a1 → getElem! (List.set a1 (Int.toNat j) x) ∘ Int.toNat = Function.update (getElem! a1 ∘ Int.toNat) j x → numof (List.set a1 (Int.toNat j) x) (0 : ℤ) n2 = numof (data h) (0 : ℤ) (i + (1 : ℤ)) + n2 - (i + (1 : ℤ)) ∧ (∀(j1 : ℤ), (0 : ℤ) ≤ j1 ∧ j1 < n2 → neq ((List.set a1 (Int.toNat j) x)[Int.toNat j1]!) dummy → view h (keym1 ((List.set a1 (Int.toNat j) x)[Int.toNat j1]!)) = true ∧ Function.update l (keym1 x) j (keym1 ((List.set a1 (Int.toNat j) x)[Int.toNat j1]!)) = j1) ∧ (∀(x1 : key), view h (keym1 x1) = true → (if loc h (keym1 x1) < i + (1 : ℤ) then let j2 : ℤ := Function.update l (keym1 x) j (keym1 x1); ((0 : ℤ) ≤ j2 ∧ j2 < n2) ∧ eq ((List.set a1 (Int.toNat j) x)[Int.toNat j2]!) x1 ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < n2 → between (bucket x1 n2) k j2 → neq ((List.set a1 (Int.toNat j) x)[Int.toNat k]!) x1 ∧ neq ((List.set a1 (Int.toNat j) x)[Int.toNat k]!) dummy) else ∀(j2 : ℤ), (0 : ℤ) ≤ j2 ∧ j2 < n2 → neq ((List.set a1 (Int.toNat j) x)[Int.toNat j2]!) x1)))) else numof a1 (0 : ℤ) n2 = numof (data h) (0 : ℤ) (i + (1 : ℤ)) + n2 - (i + (1 : ℤ)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < n2 → neq (a1[Int.toNat j]!) dummy → view h (keym1 (a1[Int.toNat j]!)) = true ∧ l (keym1 (a1[Int.toNat j]!)) = j) ∧ (∀(x1 : key), view h (keym1 x1) = true → (if loc h (keym1 x1) < i + (1 : ℤ) then let j2 : ℤ := l (keym1 x1); ((0 : ℤ) ≤ j2 ∧ j2 < n2) ∧ eq (a1[Int.toNat j2]!) x1 ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < n2 → between (bucket x1 n2) k j2 → neq (a1[Int.toNat k]!) x1 ∧ neq (a1[Int.toNat k]!) dummy) else ∀(j2 : ℤ), (0 : ℤ) ≤ j2 ∧ j2 < n2 → neq (a1[Int.toNat j2]!) x1)))))) ∧ (numof a1 (0 : ℤ) n2 = numof (data h) (0 : ℤ) (o2 + (1 : ℤ)) + n2 - (o2 + (1 : ℤ)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < n2 → neq (a1[Int.toNat j]!) dummy → view h (keym1 (a1[Int.toNat j]!)) = true ∧ l (keym1 (a1[Int.toNat j]!)) = j) ∧ (∀(x : key), view h (keym1 x) = true → (if loc h (keym1 x) < o2 + (1 : ℤ) then let j2 : ℤ := l (keym1 x); ((0 : ℤ) ≤ j2 ∧ j2 < n2) ∧ eq (a1[Int.toNat j2]!) x ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < n2 → between (bucket x n2) k j2 → neq (a1[Int.toNat k]!) x ∧ neq (a1[Int.toNat k]!) dummy) else ∀(j2 : ℤ), (0 : ℤ) ≤ j2 ∧ j2 < n2 → neq (a1[Int.toNat j2]!) x)) → (∀(h1 : t), (((0 : ℤ) ≤ size h ∧ size h < Int.ofNat (List.length a1)) ∧ (let n3 : ℤ := Int.ofNat (List.length a1); size h + numof a1 (0 : ℤ) n3 = n3) ∧ valid a1 (view h) l) ∧ (l = loc h1 ∧ view h = view h1 ∧ a1 = data h1 ∧ size h = size h1 → Int.ofNat (List.length (data h1)) = (2 : ℤ) * Int.ofNat (List.length (data h))))))) ∧ (o2 + (1 : ℤ) < (0 : ℤ) → (∀(h1 : t), (((0 : ℤ) ≤ size h ∧ size h < Int.ofNat (List.length a)) ∧ (let n3 : ℤ := Int.ofNat (List.length a); size h + numof a (0 : ℤ) n3 = n3) ∧ valid a (view h) o1) ∧ (o1 = loc h1 ∧ view h = view h1 ∧ a = data h1 ∧ size h = size h1 → Int.ofNat (List.length (data h1)) = (2 : ℤ) * Int.ofNat (List.length (data h)))))))
  := sorry
end linear_probing_LinearProbing_resizeqtvc
