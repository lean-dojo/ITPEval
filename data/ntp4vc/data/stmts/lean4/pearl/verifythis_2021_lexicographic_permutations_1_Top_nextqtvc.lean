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
namespace verifythis_2021_lexicographic_permutations_1_Top_nextqtvc
axiom elt : Type
axiom inhabited_axiom_elt : Inhabited elt
attribute [instance] inhabited_axiom_elt
axiom permutation : Type
axiom inhabited_axiom_permutation : Inhabited permutation
attribute [instance] inhabited_axiom_permutation
noncomputable def lt (p : List ℤ) (q : List ℤ) := (List.length p = List.length q ∧ (0 : ℤ) < Int.ofNat (List.length q)) ∧ (∃(i : ℤ), ((0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length p)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < i → p[Int.toNat j]! = q[Int.toNat j]!) ∧ p[Int.toNat i]! < q[Int.toNat i]!)
axiom iseq :  {α : Type} -> [Inhabited α] -> α -> List α -> ℤ -> Bool
axiom iseq'def {α : Type} [Inhabited α] (x : α) (s : List α) (i : ℤ) : (iseq x s i = true) = (s[Int.toNat i]! = x)
noncomputable def occ {α : Type} [Inhabited α] (x : α) (s : List α) (l : ℤ) (u : ℤ) := NumOf.numof (iseq x s) l u
noncomputable def occ_all {α : Type} [Inhabited α] (x : α) (s : List α) := occ x s (0 : ℤ) (Int.ofNat (List.length s))
noncomputable def is_permutation_of (p : List ℤ) (a : List ℤ) := List.length p = List.length a ∧ (∀(x : ℤ), occ_all x p = occ_all x a)
noncomputable def descending (s : List ℤ) (lo : ℤ) (hi : ℤ) := ((0 : ℤ) ≤ lo ∧ lo ≤ hi ∧ hi ≤ Int.ofNat (List.length s)) ∧ (∀(i : ℤ) (j : ℤ), lo ≤ i ∧ i ≤ j ∧ j < hi → s[Int.toNat j]! ≤ s[Int.toNat i]!)
noncomputable def ascending (s : List ℤ) (lo : ℤ) (hi : ℤ) := ((0 : ℤ) ≤ lo ∧ lo ≤ hi ∧ hi ≤ Int.ofNat (List.length s)) ∧ (∀(i : ℤ) (j : ℤ), lo ≤ i ∧ i ≤ j ∧ j < hi → s[Int.toNat i]! ≤ s[Int.toNat j]!)
axiom to_seq : List ℤ -> List ℤ
axiom to_seq'spec'0 (a : List ℤ) : List.length (to_seq a) = List.length a
axiom to_seq'spec (i : ℤ) (a : List ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < Int.ofNat (List.length (to_seq a))) : (to_seq a)[Int.toNat i]! = a[Int.toNat i]!
theorem next'vc (a : List ℤ) (a0 : List ℤ) (fact0 : List.length a = List.length a0) (fact1 : is_permutation_of (to_seq a) a0) : let n : ℤ := Int.ofNat (List.length a); let o1 : ℤ := n - (1 : ℤ); ((-(1 : ℤ) ≤ o1 ∧ o1 < n) ∧ (o1 = -(1 : ℤ) ∧ n = (0 : ℤ) ∨ (0 : ℤ) ≤ o1 ∧ descending (to_seq a) o1 n)) ∧ (∀(i : ℤ), (-(1 : ℤ) ≤ i ∧ i < n) ∧ (i = -(1 : ℤ) ∧ n = (0 : ℤ) ∨ (0 : ℤ) ≤ i ∧ descending (to_seq a) i n) → ((0 : ℤ) < i → ((0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length a)) ∧ (let o2 : ℤ := i - (1 : ℤ); (0 : ℤ) ≤ o2 ∧ o2 < Int.ofNat (List.length a))) ∧ (∀(o2 : Bool), (if (0 : ℤ) < i then o2 = (if a[Int.toNat i]! ≤ a[Int.toNat (i - (1 : ℤ))]! then true else false) else o2 = false) → (if o2 = true then ((0 : ℤ) ≤ i ∧ i - (1 : ℤ) < i) ∧ (-(1 : ℤ) ≤ i - (1 : ℤ) ∧ i - (1 : ℤ) < n) ∧ (i - (1 : ℤ) = -(1 : ℤ) ∧ n = (0 : ℤ) ∨ (0 : ℤ) ≤ i - (1 : ℤ) ∧ descending (to_seq a) (i - (1 : ℤ)) n) else if i ≤ (0 : ℤ) then is_permutation_of (to_seq a) a0 ∧ (∀(p : List ℤ), is_permutation_of p a0 → ¬lt (to_seq a) p) else let i0 : ℤ := i - (1 : ℤ); ((0 : ℤ) ≤ i0 ∧ i0 < Int.ofNat (List.length a)) ∧ (let x : ℤ := a[Int.toNat i0]!; let o3 : ℤ := n - (1 : ℤ); ((i ≤ o3 ∧ o3 < n) ∧ (∀(k : ℤ), o3 < k ∧ k < n → a[Int.toNat k]! ≤ x)) ∧ (∀(j : ℤ), (i ≤ j ∧ j < n) ∧ (∀(k : ℤ), j < k ∧ k < n → a[Int.toNat k]! ≤ x) → (let o4 : ℤ := i - (1 : ℤ); ((0 : ℤ) ≤ o4 ∧ o4 < Int.ofNat (List.length a)) ∧ ((0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length a)) ∧ (if a[Int.toNat j]! ≤ a[Int.toNat o4]! then ((0 : ℤ) ≤ j ∧ j - (1 : ℤ) < j) ∧ (i ≤ j - (1 : ℤ) ∧ j - (1 : ℤ) < n) ∧ (∀(k : ℤ), j - (1 : ℤ) < k ∧ k < n → a[Int.toNat k]! ≤ x) else ((0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length a)) ∧ (let z : ℤ := a[Int.toNat j]!; let o5 : ℤ := i - (1 : ℤ); (((0 : ℤ) ≤ o5 ∧ o5 < Int.ofNat (List.length a)) ∧ (0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length a)) ∧ (∀(a1 : List ℤ), List.length a1 = List.length a → a1[Int.toNat o5]! = a[Int.toNat j]! ∧ a1[Int.toNat j]! = a[Int.toNat o5]! ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length a1) → ¬k = o5 → ¬k = j → a1[Int.toNat k]! = a[Int.toNat k]!) ∧ is_permutation_of (to_seq a1) (to_seq a) → ((i0 < i ∧ i0 < n - (1 : ℤ) ∧ n - (1 : ℤ) < n) ∧ is_permutation_of (to_seq a1) a0 ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < i0 → a1[Int.toNat k]! = a[Int.toNat k]!) ∧ a1[Int.toNat i0]! = z ∧ i - i0 = n - (n - (1 : ℤ)) ∧ (∀(k : ℤ), (0 : ℤ) < k ∧ k < i - i0 → a1[Int.toNat (i0 + k)]! = a1[Int.toNat (n - k)]! ∧ a1[Int.toNat (n - k)]! = a1[Int.toNat (i0 + k)]!)) ∧ (∀(j1 : ℤ) (i1 : ℤ) (a2 : List ℤ), List.length a2 = List.length a1 → (i0 < i1 ∧ i0 < j1 ∧ j1 < n) ∧ is_permutation_of (to_seq a2) a0 ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < i0 → a2[Int.toNat k]! = a[Int.toNat k]!) ∧ a2[Int.toNat i0]! = z ∧ i1 - i0 = n - j1 ∧ (∀(k : ℤ), i1 ≤ k ∧ k ≤ j1 → a2[Int.toNat k]! = a1[Int.toNat k]!) ∧ (∀(k : ℤ), (0 : ℤ) < k ∧ k < i1 - i0 → a2[Int.toNat (i0 + k)]! = a1[Int.toNat (n - k)]! ∧ a2[Int.toNat (n - k)]! = a1[Int.toNat (i0 + k)]!) → (if i1 < j1 then (((0 : ℤ) ≤ i1 ∧ i1 < Int.ofNat (List.length a2)) ∧ (0 : ℤ) ≤ j1 ∧ j1 < Int.ofNat (List.length a2)) ∧ (∀(a3 : List ℤ), List.length a3 = List.length a2 → a3[Int.toNat i1]! = a2[Int.toNat j1]! ∧ a3[Int.toNat j1]! = a2[Int.toNat i1]! ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length a3) → ¬k = i1 → ¬k = j1 → a3[Int.toNat k]! = a2[Int.toNat k]!) ∧ is_permutation_of (to_seq a3) (to_seq a2) → ((0 : ℤ) ≤ j1 - i1 ∧ j1 - (1 : ℤ) - (i1 + (1 : ℤ)) < j1 - i1) ∧ (i0 < i1 + (1 : ℤ) ∧ i0 < j1 - (1 : ℤ) ∧ j1 - (1 : ℤ) < n) ∧ is_permutation_of (to_seq a3) a0 ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < i0 → a3[Int.toNat k]! = a[Int.toNat k]!) ∧ a3[Int.toNat i0]! = z ∧ i1 + (1 : ℤ) - i0 = n - (j1 - (1 : ℤ)) ∧ (∀(k : ℤ), i1 + (1 : ℤ) ≤ k ∧ k ≤ j1 - (1 : ℤ) → a3[Int.toNat k]! = a1[Int.toNat k]!) ∧ (∀(k : ℤ), (0 : ℤ) < k ∧ k < i1 + (1 : ℤ) - i0 → a3[Int.toNat (i0 + k)]! = a1[Int.toNat (n - k)]! ∧ a3[Int.toNat (n - k)]! = a1[Int.toNat (i0 + k)]!)) else (∀(p : List ℤ), is_permutation_of p a0 ∧ lt (to_seq a) p ∧ lt p (to_seq a2) → (let a11 : List ℤ := to_seq a; let v : ℤ := p[Int.toNat i0]!; if v = x then let o6 : ℤ := n - (1 : ℤ); let o7 : ℤ := i0 + (1 : ℤ); (o7 ≤ o6 + (1 : ℤ) → (∀(k : ℤ), i0 + (1 : ℤ) ≤ k ∧ k < o7 → p[Int.toNat k]! = a11[Int.toNat k]!) ∧ (∀(l : ℤ), (o7 ≤ l ∧ l ≤ o6) ∧ (∀(k : ℤ), i0 + (1 : ℤ) ≤ k ∧ k < l → p[Int.toNat k]! = a11[Int.toNat k]!) → p[Int.toNat l]! = a11[Int.toNat l]! ∧ (∀(k : ℤ), i0 + (1 : ℤ) ≤ k ∧ k < l + (1 : ℤ) → p[Int.toNat k]! = a11[Int.toNat k]!)) ∧ ¬(∀(k : ℤ), i0 + (1 : ℤ) ≤ k ∧ k < o6 + (1 : ℤ) → p[Int.toNat k]! = a11[Int.toNat k]!)) ∧ ¬o6 + (1 : ℤ) < o7 else v = z ∧ (let a21 : List ℤ := to_seq a2; List.length a21 = List.length a2 ∧ (∀(i2 : ℤ), (0 : ℤ) ≤ i2 ∧ i2 < Int.ofNat (List.length a21) → a21[Int.toNat i2]! = a2[Int.toNat i2]!) → (let o6 : ℤ := n - (1 : ℤ); let o7 : ℤ := i0 + (1 : ℤ); (o7 ≤ o6 + (1 : ℤ) → (∀(k : ℤ), i0 + (1 : ℤ) ≤ k ∧ k < o7 → p[Int.toNat k]! = a21[Int.toNat k]!) ∧ (∀(l : ℤ), (o7 ≤ l ∧ l ≤ o6) ∧ (∀(k : ℤ), i0 + (1 : ℤ) ≤ k ∧ k < l → p[Int.toNat k]! = a21[Int.toNat k]!) → p[Int.toNat l]! = a21[Int.toNat l]! ∧ (∀(k : ℤ), i0 + (1 : ℤ) ≤ k ∧ k < l + (1 : ℤ) → p[Int.toNat k]! = a21[Int.toNat k]!)) ∧ ¬(∀(k : ℤ), i0 + (1 : ℤ) ≤ k ∧ k < o6 + (1 : ℤ) → p[Int.toNat k]! = a21[Int.toNat k]!)) ∧ ¬o6 + (1 : ℤ) < o7)))) ∧ ((∀(p : List ℤ), ¬(is_permutation_of p a0 ∧ lt (to_seq a) p ∧ lt p (to_seq a2))) → is_permutation_of (to_seq a2) a0 ∧ lt (to_seq a) (to_seq a2) ∧ (∀(p : List ℤ), is_permutation_of p a0 → ¬(lt (to_seq a) p ∧ lt p (to_seq a2)))))))))))))))
  := sorry
end verifythis_2021_lexicographic_permutations_1_Top_nextqtvc
