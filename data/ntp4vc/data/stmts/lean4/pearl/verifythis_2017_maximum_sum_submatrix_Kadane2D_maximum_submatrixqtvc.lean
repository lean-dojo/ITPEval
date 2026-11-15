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
namespace verifythis_2017_maximum_sum_submatrix_Kadane2D_maximum_submatrixqtvc
axiom mixfix_lbrb_closure :  {α : Type} -> [Inhabited α] -> List α -> ℤ -> α
axiom mixfix_lbrb_closure_def {α : Type} [Inhabited α] (y : List α) (y1 : ℤ) : mixfix_lbrb_closure y y1 = y[Int.toNat y1]!
noncomputable def array_sum (a : List ℤ) (l : ℤ) (h : ℤ) := int.Sum.sum (mixfix_lbrb_closure a) l h
noncomputable def col (m : Matrix.matrix ℤ) (j : ℤ) (i : ℤ) := Matrix.elts m i j
axiom col_closure : Matrix.matrix ℤ -> ℤ -> ℤ -> ℤ
axiom fc : Matrix.matrix ℤ -> ℤ -> ℤ -> ℤ -> ℤ
axiom col_closure_def (y : Matrix.matrix ℤ) (y1 : ℤ) (y2 : ℤ) : col_closure y y1 y2 = col y y1 y2
axiom fc'def (m : Matrix.matrix ℤ) (rl : ℤ) (rh : ℤ) (j : ℤ) : fc m rl rh j = int.Sum.sum (col_closure m j) rl rh
noncomputable def matrix_sum (m : Matrix.matrix ℤ) (rl : ℤ) (rh : ℤ) (cl : ℤ) (ch : ℤ) := int.Sum.sum (fc m rl rh) cl ch
theorem maximum_submatrix'vc (m : Matrix.matrix ℤ) : let o1 : ℤ := Matrix.columns m; (0 : ℤ) ≤ o1 ∧ (∀(a : List ℤ), (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < o1 → a[Int.toNat i]! = (0 : ℤ)) ∧ Int.ofNat (List.length a) = o1 → (let o2 : ℤ := Matrix.rows m - (1 : ℤ); ((0 : ℤ) ≤ o2 + (1 : ℤ) → (((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ Matrix.columns m) ∧ ((0 : ℤ) = matrix_sum m (0 : ℤ) (0 : ℤ) (0 : ℤ) (0 : ℤ) ∧ (0 : ℤ) ≤ matrix_sum m (0 : ℤ) (0 : ℤ) (0 : ℤ) (0 : ℤ)) ∧ (∀(rl' : ℤ) (rh : ℤ), (0 : ℤ) ≤ rl' ∧ rl' < (0 : ℤ) → rl' ≤ rh ∧ rh ≤ Matrix.rows m → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh cl ch ≤ (0 : ℤ)))) ∧ (∀(chi : ℤ) (clo : ℤ) (rhi : ℤ) (rlo : ℤ) (maxsum : ℤ) (a1 : List ℤ), List.length a1 = List.length a → (∀(rl : ℤ), ((0 : ℤ) ≤ rl ∧ rl ≤ o2) ∧ ((0 : ℤ) ≤ rlo ∧ rlo ≤ rhi ∧ rhi ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ clo ∧ clo ≤ chi ∧ chi ≤ Matrix.columns m) ∧ (maxsum = matrix_sum m rlo rhi clo chi ∧ (0 : ℤ) ≤ matrix_sum m rlo rhi clo chi) ∧ (∀(rl' : ℤ) (rh : ℤ), (0 : ℤ) ≤ rl' ∧ rl' < rl → rl' ≤ rh ∧ rh ≤ Matrix.rows m → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh cl ch ≤ maxsum)) → (let o3 : ℤ := Matrix.columns m; ((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ o3 ∧ (0 : ℤ) + o3 ≤ Int.ofNat (List.length a1)) ∧ (∀(a2 : List ℤ), List.length a2 = List.length a1 → (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (0 : ℤ) ∨ (0 : ℤ) + o3 ≤ i ∧ i < Int.ofNat (List.length a2) → a2[Int.toNat i]! = a1[Int.toNat i]!) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (0 : ℤ) + o3 → a2[Int.toNat i]! = (0 : ℤ)) → (let o4 : ℤ := Matrix.rows m; let o5 : ℤ := rl + (1 : ℤ); (o5 ≤ o4 + (1 : ℤ) → (((0 : ℤ) ≤ rlo ∧ rlo ≤ rhi ∧ rhi ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ clo ∧ clo ≤ chi ∧ chi ≤ Matrix.columns m) ∧ (maxsum = matrix_sum m rlo rhi clo chi ∧ (0 : ℤ) ≤ matrix_sum m rlo rhi clo chi) ∧ (∀(rl' : ℤ) (rh' : ℤ), (0 : ℤ) ≤ rl' ∧ rl' ≤ rh' ∧ rh' ≤ Matrix.rows m → rl' < rl ∨ rl' = rl ∧ rh' < o5 → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh' cl ch ≤ maxsum)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < Matrix.columns m → a2[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (o5 - (1 : ℤ)))) ∧ (∀(chi1 : ℤ) (clo1 : ℤ) (rhi1 : ℤ) (rlo1 : ℤ) (maxsum1 : ℤ) (a3 : List ℤ), List.length a3 = List.length a2 → (∀(rh : ℤ), (o5 ≤ rh ∧ rh ≤ o4) ∧ ((0 : ℤ) ≤ rlo1 ∧ rlo1 ≤ rhi1 ∧ rhi1 ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ clo1 ∧ clo1 ≤ chi1 ∧ chi1 ≤ Matrix.columns m) ∧ (maxsum1 = matrix_sum m rlo1 rhi1 clo1 chi1 ∧ (0 : ℤ) ≤ matrix_sum m rlo1 rhi1 clo1 chi1) ∧ (∀(rl' : ℤ) (rh' : ℤ), (0 : ℤ) ≤ rl' ∧ rl' ≤ rh' ∧ rh' ≤ Matrix.rows m → rl' < rl ∨ rl' = rl ∧ rh' < rh → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh' cl ch ≤ maxsum1)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < Matrix.columns m → a3[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (rh - (1 : ℤ))) → (let o6 : ℤ := Matrix.columns m - (1 : ℤ); ((0 : ℤ) ≤ o6 + (1 : ℤ) → ((∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < (0 : ℤ) → a3[Int.toNat j]! = int.Sum.sum (col_closure m j) rl rh) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < Matrix.columns m → a3[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (rh - (1 : ℤ)))) ∧ (∀(a4 : List ℤ), List.length a4 = List.length a3 → (∀(c : ℤ), ((0 : ℤ) ≤ c ∧ c ≤ o6) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < c → a4[Int.toNat j]! = int.Sum.sum (col_closure m j) rl rh) ∧ (∀(j : ℤ), c ≤ j ∧ j < Matrix.columns m → a4[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (rh - (1 : ℤ))) → (let o7 : ℤ := rh - (1 : ℤ); Matrix.valid_index m o7 c ∧ ((0 : ℤ) ≤ c ∧ c < Int.ofNat (List.length a4)) ∧ (let o8 : ℤ := a4[Int.toNat c]! + Matrix.elts m o7 c; ((0 : ℤ) ≤ c ∧ c < Int.ofNat (List.length a4)) ∧ (List.length (List.set a4 (Int.toNat c) o8) = List.length a4 → getElem! (List.set a4 (Int.toNat c) o8) ∘ Int.toNat = Function.update (getElem! a4 ∘ Int.toNat) c o8 → (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < c + (1 : ℤ) → (List.set a4 (Int.toNat c) o8)[Int.toNat j]! = int.Sum.sum (col_closure m j) rl rh) ∧ (∀(j : ℤ), c + (1 : ℤ) ≤ j ∧ j < Matrix.columns m → (List.set a4 (Int.toNat c) o8)[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (rh - (1 : ℤ))))))) ∧ ((∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < o6 + (1 : ℤ) → a4[Int.toNat j]! = int.Sum.sum (col_closure m j) rl rh) ∧ (∀(j : ℤ), o6 + (1 : ℤ) ≤ j ∧ j < Matrix.columns m → a4[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (rh - (1 : ℤ))) → (∀(lo : ℤ) (hi : ℤ), ((0 : ℤ) ≤ lo ∧ lo ≤ hi ∧ hi ≤ Int.ofNat (List.length a4)) ∧ (∀(l : ℤ) (h : ℤ), (0 : ℤ) ≤ l ∧ l ≤ h ∧ h ≤ Int.ofNat (List.length a4) → array_sum a4 l h ≤ array_sum a4 lo hi) → (if maxsum1 < array_sum a4 lo hi then ((0 : ℤ) ≤ rl ∧ rl ≤ rh ∧ rh ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ lo ∧ lo ≤ hi ∧ hi ≤ Matrix.columns m) ∧ (array_sum a4 lo hi = matrix_sum m rl rh lo hi ∧ (0 : ℤ) ≤ matrix_sum m rl rh lo hi) ∧ (∀(rl' : ℤ) (rh' : ℤ), (0 : ℤ) ≤ rl' ∧ rl' ≤ rh' ∧ rh' ≤ Matrix.rows m → rl' < rl ∨ rl' = rl ∧ rh' < rh + (1 : ℤ) → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh' cl ch ≤ array_sum a4 lo hi)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < Matrix.columns m → a4[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (rh + (1 : ℤ) - (1 : ℤ))) else ((0 : ℤ) ≤ rlo1 ∧ rlo1 ≤ rhi1 ∧ rhi1 ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ clo1 ∧ clo1 ≤ chi1 ∧ chi1 ≤ Matrix.columns m) ∧ (maxsum1 = matrix_sum m rlo1 rhi1 clo1 chi1 ∧ (0 : ℤ) ≤ matrix_sum m rlo1 rhi1 clo1 chi1) ∧ (∀(rl' : ℤ) (rh' : ℤ), (0 : ℤ) ≤ rl' ∧ rl' ≤ rh' ∧ rh' ≤ Matrix.rows m → rl' < rl ∨ rl' = rl ∧ rh' < rh + (1 : ℤ) → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh' cl ch ≤ maxsum1)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < Matrix.columns m → a4[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (rh + (1 : ℤ) - (1 : ℤ)))))))) ∧ (o6 + (1 : ℤ) < (0 : ℤ) → (∀(lo : ℤ) (hi : ℤ), ((0 : ℤ) ≤ lo ∧ lo ≤ hi ∧ hi ≤ Int.ofNat (List.length a3)) ∧ (∀(l : ℤ) (h : ℤ), (0 : ℤ) ≤ l ∧ l ≤ h ∧ h ≤ Int.ofNat (List.length a3) → array_sum a3 l h ≤ array_sum a3 lo hi) → (if maxsum1 < array_sum a3 lo hi then ((0 : ℤ) ≤ rl ∧ rl ≤ rh ∧ rh ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ lo ∧ lo ≤ hi ∧ hi ≤ Matrix.columns m) ∧ (array_sum a3 lo hi = matrix_sum m rl rh lo hi ∧ (0 : ℤ) ≤ matrix_sum m rl rh lo hi) ∧ (∀(rl' : ℤ) (rh' : ℤ), (0 : ℤ) ≤ rl' ∧ rl' ≤ rh' ∧ rh' ≤ Matrix.rows m → rl' < rl ∨ rl' = rl ∧ rh' < rh + (1 : ℤ) → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh' cl ch ≤ array_sum a3 lo hi)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < Matrix.columns m → a3[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (rh + (1 : ℤ) - (1 : ℤ))) else ((0 : ℤ) ≤ rlo1 ∧ rlo1 ≤ rhi1 ∧ rhi1 ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ clo1 ∧ clo1 ≤ chi1 ∧ chi1 ≤ Matrix.columns m) ∧ (maxsum1 = matrix_sum m rlo1 rhi1 clo1 chi1 ∧ (0 : ℤ) ≤ matrix_sum m rlo1 rhi1 clo1 chi1) ∧ (∀(rl' : ℤ) (rh' : ℤ), (0 : ℤ) ≤ rl' ∧ rl' ≤ rh' ∧ rh' ≤ Matrix.rows m → rl' < rl ∨ rl' = rl ∧ rh' < rh + (1 : ℤ) → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh' cl ch ≤ maxsum1)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < Matrix.columns m → a3[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (rh + (1 : ℤ) - (1 : ℤ)))))))) ∧ (((0 : ℤ) ≤ rlo1 ∧ rlo1 ≤ rhi1 ∧ rhi1 ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ clo1 ∧ clo1 ≤ chi1 ∧ chi1 ≤ Matrix.columns m) ∧ (maxsum1 = matrix_sum m rlo1 rhi1 clo1 chi1 ∧ (0 : ℤ) ≤ matrix_sum m rlo1 rhi1 clo1 chi1) ∧ (∀(rl' : ℤ) (rh' : ℤ), (0 : ℤ) ≤ rl' ∧ rl' ≤ rh' ∧ rh' ≤ Matrix.rows m → rl' < rl ∨ rl' = rl ∧ rh' < o4 + (1 : ℤ) → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh' cl ch ≤ maxsum1)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < Matrix.columns m → a3[Int.toNat j]! = int.Sum.sum (col_closure m j) rl (o4 + (1 : ℤ) - (1 : ℤ))) → ((0 : ℤ) ≤ rlo1 ∧ rlo1 ≤ rhi1 ∧ rhi1 ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ clo1 ∧ clo1 ≤ chi1 ∧ chi1 ≤ Matrix.columns m) ∧ (maxsum1 = matrix_sum m rlo1 rhi1 clo1 chi1 ∧ (0 : ℤ) ≤ matrix_sum m rlo1 rhi1 clo1 chi1) ∧ (∀(rl' : ℤ) (rh : ℤ), (0 : ℤ) ≤ rl' ∧ rl' < rl + (1 : ℤ) → rl' ≤ rh ∧ rh ≤ Matrix.rows m → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh cl ch ≤ maxsum1))))) ∧ (o4 + (1 : ℤ) < o5 → ((0 : ℤ) ≤ rlo ∧ rlo ≤ rhi ∧ rhi ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ clo ∧ clo ≤ chi ∧ chi ≤ Matrix.columns m) ∧ (maxsum = matrix_sum m rlo rhi clo chi ∧ (0 : ℤ) ≤ matrix_sum m rlo rhi clo chi) ∧ (∀(rl' : ℤ) (rh : ℤ), (0 : ℤ) ≤ rl' ∧ rl' < rl + (1 : ℤ) → rl' ≤ rh ∧ rh ≤ Matrix.rows m → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh cl ch ≤ maxsum))))))) ∧ (((0 : ℤ) ≤ rlo ∧ rlo ≤ rhi ∧ rhi ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ clo ∧ clo ≤ chi ∧ chi ≤ Matrix.columns m) ∧ (maxsum = matrix_sum m rlo rhi clo chi ∧ (0 : ℤ) ≤ matrix_sum m rlo rhi clo chi) ∧ (∀(rl' : ℤ) (rh : ℤ), (0 : ℤ) ≤ rl' ∧ rl' < o2 + (1 : ℤ) → rl' ≤ rh ∧ rh ≤ Matrix.rows m → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl' rh cl ch ≤ maxsum)) → ((0 : ℤ) ≤ rlo ∧ rlo ≤ rhi ∧ rhi ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ clo ∧ clo ≤ chi ∧ chi ≤ Matrix.columns m) ∧ maxsum = matrix_sum m rlo rhi clo chi ∧ (∀(rl : ℤ) (rh : ℤ), (0 : ℤ) ≤ rl ∧ rl ≤ rh ∧ rh ≤ Matrix.rows m → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl rh cl ch ≤ maxsum))))) ∧ (o2 + (1 : ℤ) < (0 : ℤ) → ((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ Matrix.rows m) ∧ ((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ Matrix.columns m) ∧ (0 : ℤ) = matrix_sum m (0 : ℤ) (0 : ℤ) (0 : ℤ) (0 : ℤ) ∧ (∀(rl : ℤ) (rh : ℤ), (0 : ℤ) ≤ rl ∧ rl ≤ rh ∧ rh ≤ Matrix.rows m → (∀(cl : ℤ) (ch : ℤ), (0 : ℤ) ≤ cl ∧ cl ≤ ch ∧ ch ≤ Matrix.columns m → matrix_sum m rl rh cl ch ≤ (0 : ℤ))))))
  := sorry
end verifythis_2017_maximum_sum_submatrix_Kadane2D_maximum_submatrixqtvc
