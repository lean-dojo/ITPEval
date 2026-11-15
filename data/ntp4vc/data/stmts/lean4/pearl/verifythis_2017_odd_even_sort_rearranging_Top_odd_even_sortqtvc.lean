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
namespace int.Sum
axiom sum : (ℤ -> ℤ) -> ℤ -> ℤ -> ℤ
axiom sum'def (b : ℤ) (a : ℤ) (f : ℤ -> ℤ) : if b ≤ a then sum f a b = (0 : ℤ) else sum f a b = sum f a (b - (1 : ℤ)) + f (b - (1 : ℤ))
axiom sum_left (a : ℤ) (b : ℤ) (f : ℤ -> ℤ) (fact0 : a < b) : sum f a b = f a + sum f (a + (1 : ℤ)) b
axiom sum_ext (a : ℤ) (b : ℤ) (f : ℤ -> ℤ) (g : ℤ -> ℤ) (fact0 : ∀(i : ℤ), a ≤ i ∧ i < b → f i = g i) : sum f a b = sum g a b
axiom sum_le (a : ℤ) (b : ℤ) (f : ℤ -> ℤ) (g : ℤ -> ℤ) (fact0 : ∀(i : ℤ), a ≤ i ∧ i < b → f i ≤ g i) : sum f a b ≤ sum g a b
axiom sum_zero (a : ℤ) (b : ℤ) (f : ℤ -> ℤ) (fact0 : ∀(i : ℤ), a ≤ i ∧ i < b → f i = (0 : ℤ)) : sum f a b = (0 : ℤ)
axiom sum_nonneg (a : ℤ) (b : ℤ) (f : ℤ -> ℤ) (fact0 : ∀(i : ℤ), a ≤ i ∧ i < b → (0 : ℤ) ≤ f i) : (0 : ℤ) ≤ sum f a b
axiom sum_decomp (a : ℤ) (b : ℤ) (c : ℤ) (f : ℤ -> ℤ) (fact0 : a ≤ b) (fact1 : b ≤ c) : sum f a c = sum f a b + sum f b c
axiom shift_left (b : ℤ) (a : ℤ) (d : ℤ) (c : ℤ) (f : ℤ -> ℤ) (g : ℤ -> ℤ) (fact0 : b - a = d - c) (fact1 : ∀(i : ℤ), a ≤ i ∧ i < b → f i = g (c + i - a)) : sum f a b = sum g c d
end int.Sum
namespace MapEq
noncomputable def map_eq_sub {α : Type} [Inhabited α] (a1 : ℤ -> α) (a2 : ℤ -> α) (l : ℤ) (u : ℤ) := ∀(i : ℤ), l ≤ i ∧ i < u → a1 i = a2 i
end MapEq
namespace MapExchange
noncomputable def exchange {α : Type} [Inhabited α] (a1 : ℤ -> α) (a2 : ℤ -> α) (l : ℤ) (u : ℤ) (i : ℤ) (j : ℤ) := (l ≤ i ∧ i < u) ∧ (l ≤ j ∧ j < u) ∧ a1 i = a2 j ∧ a1 j = a2 i ∧ (∀(k : ℤ), l ≤ k ∧ k < u → ¬k = i → ¬k = j → a1 k = a2 k)
axiom exchange_set {α : Type} [Inhabited α] (l : ℤ) (i : ℤ) (u : ℤ) (j : ℤ) (a : ℤ -> α) (fact0 : l ≤ i) (fact1 : i < u) (fact2 : l ≤ j) (fact3 : j < u) : exchange a (Function.update (Function.update a i (a j)) j (a i)) l u i j
end MapExchange
namespace MapPermut
noncomputable def permut {α : Type} [Inhabited α] (m1 : ℤ -> α) (m2 : ℤ -> α) (l : ℤ) (u : ℤ) := ∀(v : α), Lean4Why3.map_occ v m1 l u = Lean4Why3.map_occ v m2 l u
axiom permut_trans {α : Type} [Inhabited α] (a1 : ℤ -> α) (a2 : ℤ -> α) (l : ℤ) (u : ℤ) (a3 : ℤ -> α) (fact0 : permut a1 a2 l u) (fact1 : permut a2 a3 l u) : permut a1 a3 l u
axiom permut_exists {α : Type} [Inhabited α] (a1 : ℤ -> α) (a2 : ℤ -> α) (l : ℤ) (u : ℤ) (i : ℤ) (fact0 : permut a1 a2 l u) (fact1 : l ≤ i) (fact2 : i < u) : ∃(j : ℤ), (l ≤ j ∧ j < u) ∧ a1 j = a2 i
end MapPermut
namespace IntArraySorted
noncomputable def sorted_sub (a : ℤ -> ℤ) (l : ℤ) (u : ℤ) := ∀(i1 : ℤ) (i2 : ℤ), l ≤ i1 ∧ i1 ≤ i2 ∧ i2 < u → a i1 ≤ a i2
noncomputable def sorted_sub1 (a : List ℤ) (l : ℤ) (u : ℤ) := sorted_sub (getElem! a ∘ Int.toNat) l u
noncomputable def sorted (a : List ℤ) := sorted_sub (getElem! a ∘ Int.toNat) (0 : ℤ) (Int.ofNat (List.length a))
end IntArraySorted
namespace verifythis_2017_odd_even_sort_rearranging_Top_odd_even_sortqtvc
axiom array_max : List ℤ -> ℤ
axiom array_max'spec (j : ℤ) (a : List ℤ) (fact0 : (0 : ℤ) ≤ j) (fact1 : j < Int.ofNat (List.length a)) : a[Int.toNat j]! ≤ array_max a
noncomputable def aux (a : ℤ -> ℤ) (m : ℤ) (i : ℤ) := i * (m - a i)
axiom aux_closure : (ℤ -> ℤ) -> ℤ -> ℤ -> ℤ
axiom aux_closure_def (y : ℤ -> ℤ) (y1 : ℤ) (y2 : ℤ) : aux_closure y y1 y2 = aux y y1 y2
noncomputable def entropy (a : List ℤ) (m : ℤ) := int.Sum.sum (aux_closure (getElem! a ∘ Int.toNat) m) (0 : ℤ) (Int.ofNat (List.length a))
theorem odd_even_sort'vc (a : List ℤ) (fact0 : (0 : ℤ) < Int.ofNat (List.length a)) : let m : ℤ := array_max a; (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length a) → a[Int.toNat j]! ≤ m) → List.Perm a a ∧ (∀(ok : Bool) (a1 : List ℤ), List.length a1 = List.length a → List.Perm a a1 ∧ (ok = true → IntArraySorted.sorted a1) → (if ¬ok = true then (List.Perm a a1 ∧ ((0 : ℤ) ≤ (1 : ℤ) ∧ (1 : ℤ) ≤ Int.ofNat (List.length a1)) ∧ Odd (1 : ℤ) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < (1 : ℤ) → Odd j → a1[Int.toNat j]! ≤ a1[Int.toNat (j + (1 : ℤ))]!) ∧ (¬True → entropy a1 m < entropy a1 m)) ∧ (∀(i : ℤ) (ok1 : Bool) (a2 : List ℤ), List.length a2 = List.length a1 → List.Perm a a2 ∧ ((0 : ℤ) ≤ i ∧ i ≤ Int.ofNat (List.length a2)) ∧ Odd i ∧ (ok1 = true → entropy a2 m = entropy a1 m) ∧ (ok1 = true → (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < i → Odd j → a2[Int.toNat j]! ≤ a2[Int.toNat (j + (1 : ℤ))]!)) ∧ (¬ok1 = true → entropy a2 m < entropy a1 m) → (if i < Int.ofNat (List.length a2) - (1 : ℤ) then let o1 : ℤ := i + (1 : ℤ); ((0 : ℤ) ≤ o1 ∧ o1 < Int.ofNat (List.length a2)) ∧ ((0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length a2)) ∧ (if a2[Int.toNat o1]! < a2[Int.toNat i]! then let o2 : ℤ := i + (1 : ℤ); (a2[Int.toNat o2]! < a2[Int.toNat i]! ∧ (0 : ℤ) ≤ i ∧ i < o2 ∧ o2 < Int.ofNat (List.length a2)) ∧ (∀(a3 : List ℤ), List.length a3 = List.length a2 → Lean4Why3.arrayExchange a2 a3 i o2 ∧ entropy a3 m < entropy a2 m → ((0 : ℤ) ≤ Int.ofNat (List.length a2) - i ∧ Int.ofNat (List.length a3) - (i + (2 : ℤ)) < Int.ofNat (List.length a2) - i) ∧ List.Perm a a3 ∧ ((0 : ℤ) ≤ i + (2 : ℤ) ∧ i + (2 : ℤ) ≤ Int.ofNat (List.length a3)) ∧ Odd (i + (2 : ℤ)) ∧ (false = true → entropy a3 m = entropy a1 m) ∧ (false = true → (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < i + (2 : ℤ) → Odd j → a3[Int.toNat j]! ≤ a3[Int.toNat (j + (1 : ℤ))]!)) ∧ (¬false = true → entropy a3 m < entropy a1 m)) else ((0 : ℤ) ≤ Int.ofNat (List.length a2) - i ∧ Int.ofNat (List.length a2) - (i + (2 : ℤ)) < Int.ofNat (List.length a2) - i) ∧ List.Perm a a2 ∧ ((0 : ℤ) ≤ i + (2 : ℤ) ∧ i + (2 : ℤ) ≤ Int.ofNat (List.length a2)) ∧ Odd (i + (2 : ℤ)) ∧ (ok1 = true → entropy a2 m = entropy a1 m) ∧ (ok1 = true → (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < i + (2 : ℤ) → Odd j → a2[Int.toNat j]! ≤ a2[Int.toNat (j + (1 : ℤ))]!)) ∧ (¬ok1 = true → entropy a2 m < entropy a1 m)) else (List.Perm a a2 ∧ ((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ Int.ofNat (List.length a2)) ∧ Even (0 : ℤ) ∧ (ok1 = true → entropy a2 m = entropy a1 m) ∧ (ok1 = true → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length a2) - (1 : ℤ)) ∧ Odd j → a2[Int.toNat j]! ≤ a2[Int.toNat (j + (1 : ℤ))]!)) ∧ (ok1 = true → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < (0 : ℤ)) ∧ Even j → a2[Int.toNat j]! ≤ a2[Int.toNat (j + (1 : ℤ))]!)) ∧ (¬ok1 = true → entropy a2 m < entropy a1 m)) ∧ (∀(i1 : ℤ) (ok2 : Bool) (a3 : List ℤ), List.length a3 = List.length a2 → List.Perm a a3 ∧ ((0 : ℤ) ≤ i1 ∧ i1 ≤ Int.ofNat (List.length a3)) ∧ Even i1 ∧ (ok2 = true → entropy a3 m = entropy a1 m) ∧ (ok2 = true → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length a3) - (1 : ℤ)) ∧ Odd j → a3[Int.toNat j]! ≤ a3[Int.toNat (j + (1 : ℤ))]!)) ∧ (ok2 = true → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < i1) ∧ Even j → a3[Int.toNat j]! ≤ a3[Int.toNat (j + (1 : ℤ))]!)) ∧ (¬ok2 = true → entropy a3 m < entropy a1 m) → (if i1 < Int.ofNat (List.length a3) - (1 : ℤ) then let o1 : ℤ := i1 + (1 : ℤ); ((0 : ℤ) ≤ o1 ∧ o1 < Int.ofNat (List.length a3)) ∧ ((0 : ℤ) ≤ i1 ∧ i1 < Int.ofNat (List.length a3)) ∧ (if a3[Int.toNat o1]! < a3[Int.toNat i1]! then let o2 : ℤ := i1 + (1 : ℤ); (a3[Int.toNat o2]! < a3[Int.toNat i1]! ∧ (0 : ℤ) ≤ i1 ∧ i1 < o2 ∧ o2 < Int.ofNat (List.length a3)) ∧ (∀(a4 : List ℤ), List.length a4 = List.length a3 → Lean4Why3.arrayExchange a3 a4 i1 o2 ∧ entropy a4 m < entropy a3 m → ((0 : ℤ) ≤ Int.ofNat (List.length a3) - i1 ∧ Int.ofNat (List.length a4) - (i1 + (2 : ℤ)) < Int.ofNat (List.length a3) - i1) ∧ List.Perm a a4 ∧ ((0 : ℤ) ≤ i1 + (2 : ℤ) ∧ i1 + (2 : ℤ) ≤ Int.ofNat (List.length a4)) ∧ Even (i1 + (2 : ℤ)) ∧ (false = true → entropy a4 m = entropy a1 m) ∧ (false = true → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length a4) - (1 : ℤ)) ∧ Odd j → a4[Int.toNat j]! ≤ a4[Int.toNat (j + (1 : ℤ))]!)) ∧ (false = true → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < i1 + (2 : ℤ)) ∧ Even j → a4[Int.toNat j]! ≤ a4[Int.toNat (j + (1 : ℤ))]!)) ∧ (¬false = true → entropy a4 m < entropy a1 m)) else ((0 : ℤ) ≤ Int.ofNat (List.length a3) - i1 ∧ Int.ofNat (List.length a3) - (i1 + (2 : ℤ)) < Int.ofNat (List.length a3) - i1) ∧ List.Perm a a3 ∧ ((0 : ℤ) ≤ i1 + (2 : ℤ) ∧ i1 + (2 : ℤ) ≤ Int.ofNat (List.length a3)) ∧ Even (i1 + (2 : ℤ)) ∧ (ok2 = true → entropy a3 m = entropy a1 m) ∧ (ok2 = true → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length a3) - (1 : ℤ)) ∧ Odd j → a3[Int.toNat j]! ≤ a3[Int.toNat (j + (1 : ℤ))]!)) ∧ (ok2 = true → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < i1 + (2 : ℤ)) ∧ Even j → a3[Int.toNat j]! ≤ a3[Int.toNat (j + (1 : ℤ))]!)) ∧ (¬ok2 = true → entropy a3 m < entropy a1 m)) else ((0 : ℤ) ≤ entropy a1 m + (if ok = true then (0 : ℤ) else (1 : ℤ)) ∧ entropy a3 m + (if ok2 = true then (0 : ℤ) else (1 : ℤ)) < entropy a1 m + (if ok = true then (0 : ℤ) else (1 : ℤ))) ∧ List.Perm a a3 ∧ (ok2 = true → IntArraySorted.sorted a3))))) else IntArraySorted.sorted a1 ∧ List.Perm a a1))
  := sorry
end verifythis_2017_odd_even_sort_rearranging_Top_odd_even_sortqtvc
