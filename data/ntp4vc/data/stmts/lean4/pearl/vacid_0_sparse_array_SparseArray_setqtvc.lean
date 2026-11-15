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

namespace MapInjection
noncomputable def injective (a : ℤ -> ℤ) (n : ℤ) := ∀(i : ℤ) (j : ℤ), (0 : ℤ) ≤ i ∧ i < n → (0 : ℤ) ≤ j ∧ j < n → ¬i = j → ¬a i = a j
noncomputable def surjective (a : ℤ -> ℤ) (n : ℤ) := ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → (∃(j : ℤ), ((0 : ℤ) ≤ j ∧ j < n) ∧ a j = i)
noncomputable def range (a : ℤ -> ℤ) (n : ℤ) := ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → (0 : ℤ) ≤ a i ∧ a i < n
axiom injective_surjective (a : ℤ -> ℤ) (n : ℤ) (fact0 : injective a n) (fact1 : range a n) : surjective a n
axiom injection_occ (m : ℤ -> ℤ) (n : ℤ) : injective m n = (∀(v : ℤ), Int.ofNat (Lean4Why3.map_occ v m (0 : ℤ) n) ≤ (1 : ℤ))
end MapInjection
namespace vacid_0_sparse_array_SparseArray_setqtvc
axiom sparse_array : Type -> Type
axiom inhabited_axiom_sparse_array {α : Type} [Inhabited α] : Inhabited (sparse_array α)
attribute [instance] inhabited_axiom_sparse_array
axiom values :  {α : Type} -> [Inhabited α] -> sparse_array α -> List α
axiom index :  {α : Type} -> [Inhabited α] -> sparse_array α -> List ℤ
axiom back :  {α : Type} -> [Inhabited α] -> sparse_array α -> List ℤ
axiom card :  {α : Type} -> [Inhabited α] -> sparse_array α -> ℤ
axiom def1 :  {α : Type} -> [Inhabited α] -> sparse_array α -> α
axiom sparse_array'invariant {α : Type} [Inhabited α] (self : sparse_array α) : (0 : ℤ) ≤ card self ∧ card self ≤ Int.ofNat (List.length (values self)) ∧ Int.ofNat (List.length (values self)) ≤ (1000 : ℤ) ∧ List.length (values self) = List.length (index self) ∧ List.length (index self) = List.length (back self) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < card self → ((0 : ℤ) ≤ (back self)[Int.toNat i]! ∧ (back self)[Int.toNat i]! < Int.ofNat (List.length (values self))) ∧ (index self)[Int.toNat ((back self)[Int.toNat i]!)]! = i)
noncomputable def sparse_array'eq {α : Type} [Inhabited α] (a : sparse_array α) (b : sparse_array α) := values a = values b ∧ index a = index b ∧ back a = back b ∧ card a = card b ∧ def1 a = def1 b
axiom sparse_array'inj {α : Type} [Inhabited α] (a : sparse_array α) (b : sparse_array α) (fact0 : sparse_array'eq a b) : a = b
noncomputable def is_elt {α : Type} [Inhabited α] (a : sparse_array α) (i : ℤ) := ((0 : ℤ) ≤ (index a)[Int.toNat i]! ∧ (index a)[Int.toNat i]! < card a) ∧ (back a)[Int.toNat ((index a)[Int.toNat i]!)]! = i
noncomputable def value {α : Type} [Inhabited α] (a : sparse_array α) (i : ℤ) := if is_elt a i then (values a)[Int.toNat i]! else def1 a
noncomputable def length {α : Type} [Inhabited α] (a : sparse_array α) := Int.ofNat (List.length (values a))
theorem set'vc {α : Type} [Inhabited α] (i : ℤ) (a : sparse_array α) (v : α) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < length a) : let o1 : List α := values a; ((0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o1)) ∧ (∀(a1 : sparse_array α), List.length (List.set o1 (Int.toNat i) v) = List.length o1 → List.length (List.set o1 (Int.toNat i) v) = List.length (values a) → getElem! (List.set o1 (Int.toNat i) v) ∘ Int.toNat = Function.update (getElem! o1 ∘ Int.toNat) i v → (((0 : ℤ) ≤ card a ∧ card a ≤ Int.ofNat (List.length (List.set o1 (Int.toNat i) v)) ∧ Int.ofNat (List.length (List.set o1 (Int.toNat i) v)) ≤ (1000 : ℤ)) ∧ (List.length (List.set o1 (Int.toNat i) v) = List.length (index a) ∧ List.length (index a) = List.length (back a)) ∧ (∀(i1 : ℤ), (0 : ℤ) ≤ i1 ∧ i1 < card a → ((0 : ℤ) ≤ (back a)[Int.toNat i1]! ∧ (back a)[Int.toNat i1]! < Int.ofNat (List.length (List.set o1 (Int.toNat i) v))) ∧ (index a)[Int.toNat ((back a)[Int.toNat i1]!)]! = i1)) ∧ (def1 a = def1 a1 ∧ card a = card a1 ∧ back a = back a1 ∧ index a = index a1 ∧ List.set o1 (Int.toNat i) v = values a1 → ((0 : ℤ) ≤ i ∧ i < length a1) ∧ (if ¬is_elt a1 i then let o2 : ℤ := card a1; let o3 : List ℤ := index a1; ((0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3)) ∧ (List.length (List.set o3 (Int.toNat i) o2) = List.length o3 → List.length (List.set o3 (Int.toNat i) o2) = List.length (index a1) → getElem! (List.set o3 (Int.toNat i) o2) ∘ Int.toNat = Function.update (getElem! o3 ∘ Int.toNat) i o2 → ((0 : ℤ) ≤ card a1 ∧ card a1 < Int.ofNat (List.length (back a1))) ∧ (List.length (List.set (back a1) (Int.toNat (card a1)) i) = List.length (back a1) → List.length (List.set (back a1) (Int.toNat (card a1)) i) = List.length (back a1) → getElem! (List.set (back a1) (Int.toNat (card a1)) i) ∘ Int.toNat = Function.update (getElem! (back a1) ∘ Int.toNat) (card a1) i → (∀(a2 : sparse_array α), (((0 : ℤ) ≤ card a1 + (1 : ℤ) ∧ card a1 + (1 : ℤ) ≤ Int.ofNat (List.length (values a1)) ∧ Int.ofNat (List.length (values a1)) ≤ (1000 : ℤ)) ∧ (List.length (values a1) = List.length (List.set o3 (Int.toNat i) o2) ∧ List.length (List.set o3 (Int.toNat i) o2) = List.length (List.set (back a1) (Int.toNat (card a1)) i)) ∧ (∀(i1 : ℤ), (0 : ℤ) ≤ i1 ∧ i1 < card a1 + (1 : ℤ) → ((0 : ℤ) ≤ (List.set (back a1) (Int.toNat (card a1)) i)[Int.toNat i1]! ∧ (List.set (back a1) (Int.toNat (card a1)) i)[Int.toNat i1]! < Int.ofNat (List.length (values a1))) ∧ (List.set o3 (Int.toNat i) o2)[Int.toNat ((List.set (back a1) (Int.toNat (card a1)) i)[Int.toNat i1]!)]! = i1)) ∧ (def1 a1 = def1 a2 ∧ card a1 + (1 : ℤ) = card a2 ∧ List.set (back a1) (Int.toNat (card a1)) i = back a2 ∧ List.set o3 (Int.toNat i) o2 = index a2 ∧ values a1 = values a2 → value a2 i = v ∧ (∀(j : ℤ), ¬j = i → value a2 j = value a j))))) else value a1 i = v ∧ (∀(j : ℤ), ¬j = i → value a1 j = value a j))))
  := sorry
end vacid_0_sparse_array_SparseArray_setqtvc
