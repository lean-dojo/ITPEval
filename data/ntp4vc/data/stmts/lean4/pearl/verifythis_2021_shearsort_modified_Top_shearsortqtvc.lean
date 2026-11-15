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
namespace Matrix
axiom matrix : Type -> Type
axiom inhabited_axiom_matrix {α : Type} [Inhabited α] : Inhabited (matrix α)
attribute [instance] inhabited_axiom_matrix
axiom elts :  {α : Type} -> [Inhabited α] -> matrix α -> ℤ -> ℤ -> α
axiom rows :  {α : Type} -> [Inhabited α] -> matrix α -> ℤ
axiom columns :  {α : Type} -> [Inhabited α] -> matrix α -> ℤ
axiom matrix'invariant {α : Type} [Inhabited α] (self : matrix α) : (0 : ℤ) ≤ rows self ∧ (0 : ℤ) ≤ columns self
noncomputable def valid_index {α : Type} [Inhabited α] (a : matrix α) (r : ℤ) (c : ℤ) := ((0 : ℤ) ≤ r ∧ r < rows a) ∧ (0 : ℤ) ≤ c ∧ c < columns a
noncomputable def get {α : Type} [Inhabited α] (a : matrix α) (r : ℤ) (c : ℤ) := elts a r c
axiom update :  {α : Type} -> [Inhabited α] -> matrix α -> ℤ -> ℤ -> α -> matrix α
axiom update'spec'1 {α : Type} [Inhabited α] (a : matrix α) (r : ℤ) (c : ℤ) (v : α) : rows (update a r c v) = rows a
axiom update'spec'0 {α : Type} [Inhabited α] (a : matrix α) (r : ℤ) (c : ℤ) (v : α) : columns (update a r c v) = columns a
axiom update'spec {α : Type} [Inhabited α] (a : matrix α) (r : ℤ) (c : ℤ) (v : α) : elts (update a r c v) = Function.update (elts a) r (Function.update (elts a r) c v)
end Matrix
namespace verifythis_2021_shearsort_modified_Top_shearsortqtvc
axiom fc : ℤ -> Matrix.matrix ℤ -> ℤ -> ℤ
axiom fc'def (x : ℤ) (m : Matrix.matrix ℤ) (i : ℤ) : fc x m i = Int.ofNat (Lean4Why3.map_occ x (Matrix.elts m i) (0 : ℤ) (Matrix.columns m))
noncomputable def mocc (x : ℤ) (m : Matrix.matrix ℤ) := int.Sum.sum (fc x m) (0 : ℤ) (Matrix.rows m)
noncomputable def lt (i : ℤ) (j : ℤ) (k : ℤ) (l : ℤ) := i < k ∨ i = k ∧ (if Int.tmod i (2 : ℤ) = (0 : ℤ) then j < l else l < j)
noncomputable def snake_order (m : Matrix.matrix ℤ) := let rw : ℤ := Matrix.rows m; let cl : ℤ := Matrix.columns m; ∀(i : ℤ) (j : ℤ) (k : ℤ) (l : ℤ), (0 : ℤ) ≤ i ∧ i < rw → (0 : ℤ) ≤ j ∧ j < cl → (0 : ℤ) ≤ k ∧ k < rw → (0 : ℤ) ≤ l ∧ l < cl → lt i j k l → Matrix.elts m i j ≤ Matrix.elts m k l
axiom fc1 : Matrix.matrix ℤ -> ℤ -> ℤ -> ℤ -> ℤ -> Bool
axiom fc2 : Matrix.matrix ℤ -> ℤ -> ℤ -> ℤ -> ℤ
axiom fc3 : Matrix.matrix ℤ -> ℤ -> ℤ -> ℤ
axiom fc4 : Matrix.matrix ℤ -> ℤ -> ℤ
axiom fc'def1 (m : Matrix.matrix ℤ) (i : ℤ) (j : ℤ) (k : ℤ) (l : ℤ) : (fc1 m i j k l = true) = (lt i j k l ∧ Matrix.elts m k l < Matrix.elts m i j)
axiom fc'def2 (m : Matrix.matrix ℤ) (i : ℤ) (j : ℤ) (k : ℤ) : fc2 m i j k = NumOf.numof (fc1 m i j k) (0 : ℤ) (Matrix.columns m)
axiom fc'def3 (m : Matrix.matrix ℤ) (i : ℤ) (j : ℤ) : fc3 m i j = int.Sum.sum (fc2 m i j) (0 : ℤ) (Matrix.rows m)
axiom fc'def4 (m : Matrix.matrix ℤ) (i : ℤ) : fc4 m i = int.Sum.sum (fc3 m i) (0 : ℤ) (Matrix.columns m)
noncomputable def inversions (m : Matrix.matrix ℤ) := int.Sum.sum (fc4 m) (0 : ℤ) (Matrix.rows m)
noncomputable def sorted_row (m : Matrix.matrix ℤ) (row : ℤ) (ascending : Bool) := ((0 : ℤ) ≤ row ∧ row < Matrix.rows m) ∧ (if ascending = true then ∀(j : ℤ) (l : ℤ), (0 : ℤ) ≤ j ∧ j ≤ l ∧ l < Matrix.columns m → Matrix.elts m row j ≤ Matrix.elts m row l else ∀(j : ℤ) (l : ℤ), (0 : ℤ) ≤ j ∧ j ≤ l ∧ l < Matrix.columns m → Matrix.elts m row l ≤ Matrix.elts m row j)
noncomputable def sorted_column (m : Matrix.matrix ℤ) (column : ℤ) := ((0 : ℤ) ≤ column ∧ column < Matrix.columns m) ∧ (∀(i : ℤ) (k : ℤ), (0 : ℤ) ≤ i ∧ i ≤ k ∧ k < Matrix.rows m → Matrix.elts m i column ≤ Matrix.elts m k column)
theorem shearsort'vc (m : Matrix.matrix ℤ) (m1 : Matrix.matrix ℤ) (fact0 : Matrix.rows m = Matrix.columns m) (fact1 : Matrix.rows m1 = Matrix.rows m) (fact2 : Matrix.columns m1 = Matrix.columns m) (fact3 : ∀(x : ℤ), mocc x m1 = mocc x m) : let o1 : ℤ := Matrix.columns m - (1 : ℤ); ((0 : ℤ) ≤ o1 + (1 : ℤ) → ((∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < (0 : ℤ) → sorted_row m1 k (if Int.tmod k (2 : ℤ) = (0 : ℤ) then true else false)) ∧ (∀(x : ℤ), mocc x m1 = mocc x m) ∧ inversions m1 ≤ inversions m1) ∧ (∀(m2 : Matrix.matrix ℤ), Matrix.rows m2 = Matrix.rows m1 ∧ Matrix.columns m2 = Matrix.columns m1 → (∀(i : ℤ), ((0 : ℤ) ≤ i ∧ i ≤ o1) ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < i → sorted_row m2 k (if Int.tmod k (2 : ℤ) = (0 : ℤ) then true else false)) ∧ (∀(x : ℤ), mocc x m2 = mocc x m) ∧ inversions m2 ≤ inversions m1 → ¬(2 : ℤ) = (0 : ℤ) ∧ ((0 : ℤ) ≤ i ∧ i < Matrix.rows m2) ∧ (∀(m3 : Matrix.matrix ℤ), Matrix.rows m3 = Matrix.rows m2 ∧ Matrix.columns m3 = Matrix.columns m2 → (∀(i1 : ℤ) (j : ℤ), (0 : ℤ) ≤ i1 ∧ i1 < Matrix.rows m3 → (0 : ℤ) ≤ j ∧ j < Matrix.columns m3 → ¬i1 = i → Matrix.elts m3 i1 j = Matrix.elts m2 i1 j) ∧ (∀(x : ℤ), mocc x m3 = mocc x m2) ∧ sorted_row m3 i (if Int.tmod i (2 : ℤ) = (0 : ℤ) then true else false) ∧ inversions m3 ≤ inversions m2 → (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < i + (1 : ℤ) → sorted_row m3 k (if Int.tmod k (2 : ℤ) = (0 : ℤ) then true else false)) ∧ (∀(x : ℤ), mocc x m3 = mocc x m) ∧ inversions m3 ≤ inversions m1)) ∧ ((∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < o1 + (1 : ℤ) → sorted_row m2 k (if Int.tmod k (2 : ℤ) = (0 : ℤ) then true else false)) ∧ (∀(x : ℤ), mocc x m2 = mocc x m) ∧ inversions m2 ≤ inversions m1 → (let o2 : ℤ := Matrix.columns m - (1 : ℤ); ((0 : ℤ) ≤ o2 + (1 : ℤ) → ((∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < (0 : ℤ) → sorted_column m2 l) ∧ (∀(x : ℤ), mocc x m2 = mocc x m) ∧ inversions m2 ≤ inversions m2) ∧ (∀(nochange : Bool) (m3 : Matrix.matrix ℤ), Matrix.rows m3 = Matrix.rows m2 ∧ Matrix.columns m3 = Matrix.columns m2 → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j ≤ o2) ∧ (nochange = true → (∀(i : ℤ) (j1 : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m3 → (0 : ℤ) ≤ j1 ∧ j1 < Matrix.columns m3 → Matrix.elts m3 i j1 = Matrix.elts m2 i j1)) ∧ (∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < j → sorted_column m3 l) ∧ (∀(x : ℤ), mocc x m3 = mocc x m) ∧ inversions m3 ≤ inversions m2 ∧ (¬nochange = true → inversions m3 < inversions m2) → ((0 : ℤ) ≤ j ∧ j < Matrix.columns m3) ∧ (∀(m4 : Matrix.matrix ℤ), Matrix.rows m4 = Matrix.rows m3 ∧ Matrix.columns m4 = Matrix.columns m3 → (∀(nch : Bool), (∀(i : ℤ) (j1 : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m4 → (0 : ℤ) ≤ j1 ∧ j1 < Matrix.columns m4 → ¬j1 = j → Matrix.elts m4 i j1 = Matrix.elts m3 i j1) ∧ (∀(x : ℤ), mocc x m4 = mocc x m3) ∧ (nch = true → (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m4 → Matrix.elts m4 i j = Matrix.elts m3 i j)) ∧ sorted_column m4 j ∧ inversions m4 ≤ inversions m3 ∧ (¬nch = true → inversions m4 < inversions m3) → (if ¬nch = true then (false = true → (∀(i : ℤ) (j1 : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m4 → (0 : ℤ) ≤ j1 ∧ j1 < Matrix.columns m4 → Matrix.elts m4 i j1 = Matrix.elts m2 i j1)) ∧ (∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < j + (1 : ℤ) → sorted_column m4 l) ∧ (∀(x : ℤ), mocc x m4 = mocc x m) ∧ inversions m4 ≤ inversions m2 ∧ (¬false = true → inversions m4 < inversions m2) else (nochange = true → (∀(i : ℤ) (j1 : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m4 → (0 : ℤ) ≤ j1 ∧ j1 < Matrix.columns m4 → Matrix.elts m4 i j1 = Matrix.elts m2 i j1)) ∧ (∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < j + (1 : ℤ) → sorted_column m4 l) ∧ (∀(x : ℤ), mocc x m4 = mocc x m) ∧ inversions m4 ≤ inversions m2 ∧ (¬nochange = true → inversions m4 < inversions m2))))) ∧ ((nochange = true → (∀(i : ℤ) (j : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m3 → (0 : ℤ) ≤ j ∧ j < Matrix.columns m3 → Matrix.elts m3 i j = Matrix.elts m2 i j)) ∧ (∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < o2 + (1 : ℤ) → sorted_column m3 l) ∧ (∀(x : ℤ), mocc x m3 = mocc x m) ∧ inversions m3 ≤ inversions m2 ∧ (¬nochange = true → inversions m3 < inversions m2) → (if nochange = true then (∀(i : ℤ) (j : ℤ) (k : ℤ) (l : ℤ), ((0 : ℤ) ≤ i ∧ i < Matrix.columns m) ∧ ((0 : ℤ) ≤ j ∧ j < Matrix.columns m) ∧ ((0 : ℤ) ≤ k ∧ k < Matrix.columns m) ∧ ((0 : ℤ) ≤ l ∧ l < Matrix.columns m) ∧ lt i j k l → Matrix.elts m3 i j ≤ Matrix.elts m3 k l) ∧ snake_order m3 ∧ (∀(x : ℤ), mocc x m3 = mocc x m) else ((0 : ℤ) ≤ inversions m1 ∧ inversions m3 < inversions m1) ∧ (∀(x : ℤ), mocc x m3 = mocc x m))))) ∧ (o2 + (1 : ℤ) < (0 : ℤ) → (∀(i : ℤ) (j : ℤ) (k : ℤ) (l : ℤ), ((0 : ℤ) ≤ i ∧ i < Matrix.columns m) ∧ ((0 : ℤ) ≤ j ∧ j < Matrix.columns m) ∧ ((0 : ℤ) ≤ k ∧ k < Matrix.columns m) ∧ ((0 : ℤ) ≤ l ∧ l < Matrix.columns m) ∧ lt i j k l → Matrix.elts m2 i j ≤ Matrix.elts m2 k l) ∧ snake_order m2 ∧ (∀(x : ℤ), mocc x m2 = mocc x m)))))) ∧ (o1 + (1 : ℤ) < (0 : ℤ) → (let o2 : ℤ := Matrix.columns m - (1 : ℤ); ((0 : ℤ) ≤ o2 + (1 : ℤ) → ((∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < (0 : ℤ) → sorted_column m1 l) ∧ (∀(x : ℤ), mocc x m1 = mocc x m) ∧ inversions m1 ≤ inversions m1) ∧ (∀(nochange : Bool) (m2 : Matrix.matrix ℤ), Matrix.rows m2 = Matrix.rows m1 ∧ Matrix.columns m2 = Matrix.columns m1 → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j ≤ o2) ∧ (nochange = true → (∀(i : ℤ) (j1 : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m2 → (0 : ℤ) ≤ j1 ∧ j1 < Matrix.columns m2 → Matrix.elts m2 i j1 = Matrix.elts m1 i j1)) ∧ (∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < j → sorted_column m2 l) ∧ (∀(x : ℤ), mocc x m2 = mocc x m) ∧ inversions m2 ≤ inversions m1 ∧ (¬nochange = true → inversions m2 < inversions m1) → ((0 : ℤ) ≤ j ∧ j < Matrix.columns m2) ∧ (∀(m3 : Matrix.matrix ℤ), Matrix.rows m3 = Matrix.rows m2 ∧ Matrix.columns m3 = Matrix.columns m2 → (∀(nch : Bool), (∀(i : ℤ) (j1 : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m3 → (0 : ℤ) ≤ j1 ∧ j1 < Matrix.columns m3 → ¬j1 = j → Matrix.elts m3 i j1 = Matrix.elts m2 i j1) ∧ (∀(x : ℤ), mocc x m3 = mocc x m2) ∧ (nch = true → (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m3 → Matrix.elts m3 i j = Matrix.elts m2 i j)) ∧ sorted_column m3 j ∧ inversions m3 ≤ inversions m2 ∧ (¬nch = true → inversions m3 < inversions m2) → (if ¬nch = true then (false = true → (∀(i : ℤ) (j1 : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m3 → (0 : ℤ) ≤ j1 ∧ j1 < Matrix.columns m3 → Matrix.elts m3 i j1 = Matrix.elts m1 i j1)) ∧ (∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < j + (1 : ℤ) → sorted_column m3 l) ∧ (∀(x : ℤ), mocc x m3 = mocc x m) ∧ inversions m3 ≤ inversions m1 ∧ (¬false = true → inversions m3 < inversions m1) else (nochange = true → (∀(i : ℤ) (j1 : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m3 → (0 : ℤ) ≤ j1 ∧ j1 < Matrix.columns m3 → Matrix.elts m3 i j1 = Matrix.elts m1 i j1)) ∧ (∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < j + (1 : ℤ) → sorted_column m3 l) ∧ (∀(x : ℤ), mocc x m3 = mocc x m) ∧ inversions m3 ≤ inversions m1 ∧ (¬nochange = true → inversions m3 < inversions m1))))) ∧ ((nochange = true → (∀(i : ℤ) (j : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m2 → (0 : ℤ) ≤ j ∧ j < Matrix.columns m2 → Matrix.elts m2 i j = Matrix.elts m1 i j)) ∧ (∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < o2 + (1 : ℤ) → sorted_column m2 l) ∧ (∀(x : ℤ), mocc x m2 = mocc x m) ∧ inversions m2 ≤ inversions m1 ∧ (¬nochange = true → inversions m2 < inversions m1) → (if nochange = true then (∀(i : ℤ) (j : ℤ) (k : ℤ) (l : ℤ), ((0 : ℤ) ≤ i ∧ i < Matrix.columns m) ∧ ((0 : ℤ) ≤ j ∧ j < Matrix.columns m) ∧ ((0 : ℤ) ≤ k ∧ k < Matrix.columns m) ∧ ((0 : ℤ) ≤ l ∧ l < Matrix.columns m) ∧ lt i j k l → Matrix.elts m2 i j ≤ Matrix.elts m2 k l) ∧ snake_order m2 ∧ (∀(x : ℤ), mocc x m2 = mocc x m) else ((0 : ℤ) ≤ inversions m1 ∧ inversions m2 < inversions m1) ∧ (∀(x : ℤ), mocc x m2 = mocc x m))))) ∧ (o2 + (1 : ℤ) < (0 : ℤ) → (∀(i : ℤ) (j : ℤ) (k : ℤ) (l : ℤ), ((0 : ℤ) ≤ i ∧ i < Matrix.columns m) ∧ ((0 : ℤ) ≤ j ∧ j < Matrix.columns m) ∧ ((0 : ℤ) ≤ k ∧ k < Matrix.columns m) ∧ ((0 : ℤ) ≤ l ∧ l < Matrix.columns m) ∧ lt i j k l → Matrix.elts m1 i j ≤ Matrix.elts m1 k l) ∧ snake_order m1 ∧ (∀(x : ℤ), mocc x m1 = mocc x m))))
  := sorry
end verifythis_2021_shearsort_modified_Top_shearsortqtvc
