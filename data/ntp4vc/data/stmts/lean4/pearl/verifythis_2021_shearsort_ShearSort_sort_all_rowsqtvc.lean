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
namespace MapExt
noncomputable def infix_eqeq {β : Type} {α : Type} [Inhabited β] [Inhabited α] (m1 : α -> β) (m2 : α -> β) := ∀(x : α), m1 x = m2 x
axiom extensionality {β : Type} {α : Type} [Inhabited β] [Inhabited α] (m1 : α -> β) (m2 : α -> β) (fact0 : infix_eqeq m1 m2) : m1 = m2
end MapExt
namespace MapPermut
noncomputable def permut {α : Type} [Inhabited α] (m1 : ℤ -> α) (m2 : ℤ -> α) (l : ℤ) (u : ℤ) := ∀(v : α), Lean4Why3.map_occ v m1 l u = Lean4Why3.map_occ v m2 l u
axiom permut_trans {α : Type} [Inhabited α] (a1 : ℤ -> α) (a2 : ℤ -> α) (l : ℤ) (u : ℤ) (a3 : ℤ -> α) (fact0 : permut a1 a2 l u) (fact1 : permut a2 a3 l u) : permut a1 a3 l u
axiom permut_exists {α : Type} [Inhabited α] (a1 : ℤ -> α) (a2 : ℤ -> α) (l : ℤ) (u : ℤ) (i : ℤ) (fact0 : permut a1 a2 l u) (fact1 : l ≤ i) (fact2 : i < u) : ∃(j : ℤ), (l ≤ j ∧ j < u) ∧ a1 j = a2 i
end MapPermut
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
namespace verifythis_2021_shearsort_ShearSort_sort_all_rowsqtvc
axiom column :  {α : Type} -> [Inhabited α] -> Matrix.matrix α -> ℤ -> ℤ -> α
axiom column'def {α : Type} [Inhabited α] (m : Matrix.matrix α) (j : ℤ) (i : ℤ) : column m j i = Matrix.elts m i j
axiom moccf :  {α : Type} -> [Inhabited α] -> α -> (ℤ -> ℤ -> α) -> ℤ -> ℤ -> ℤ
axiom moccf'def {α : Type} [Inhabited α] (x : α) (e : ℤ -> ℤ -> α) (c : ℤ) (i : ℤ) : moccf x e c i = Int.ofNat (Lean4Why3.map_occ x (e i) (0 : ℤ) c)
noncomputable def mocc {α : Type} [Inhabited α] (x : α) (e : ℤ -> ℤ -> α) (r : ℤ) (c : ℤ) := int.Sum.sum (moccf x e c) (0 : ℤ) r
axiom compose :  {γ : Type} -> [Inhabited γ] ->  {β : Type} -> [Inhabited β] ->  {α : Type} -> [Inhabited α] -> (β -> γ) -> (α -> β) -> α -> γ
axiom compose'def {γ : Type} {α : Type} {β : Type} [Inhabited γ] [Inhabited α] [Inhabited β] (g : β -> γ) (f : α -> β) (x : α) : compose g f x = g (f x)
theorem sort_all_rows'vc (m : Matrix.matrix ℤ) : let o1 : ℤ := Matrix.rows m - (1 : ℤ); ((0 : ℤ) ≤ o1 + (1 : ℤ) → ((∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m → MapPermut.permut (Matrix.elts m i) (Matrix.elts m i) (0 : ℤ) (Matrix.columns m)) ∧ (∀(i : ℤ) (j : ℤ) (k : ℤ), ((0 : ℤ) ≤ i ∧ i < (0 : ℤ)) ∧ (0 : ℤ) ≤ j ∧ j ≤ k ∧ k < Matrix.columns m → (let a : ℤ := Matrix.elts m i j; let b : ℤ := Matrix.elts m i k; if Int.tmod i (2 : ℤ) = (0 : ℤ) then a ≤ b else b ≤ a))) ∧ (∀(m1 : Matrix.matrix ℤ), Matrix.rows m1 = Matrix.rows m ∧ Matrix.columns m1 = Matrix.columns m → (∀(tid : ℤ), ((0 : ℤ) ≤ tid ∧ tid ≤ o1) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m1 → MapPermut.permut (Matrix.elts m1 i) (Matrix.elts m i) (0 : ℤ) (Matrix.columns m1)) ∧ (∀(i : ℤ) (j : ℤ) (k : ℤ), ((0 : ℤ) ≤ i ∧ i < tid) ∧ (0 : ℤ) ≤ j ∧ j ≤ k ∧ k < Matrix.columns m1 → (let a : ℤ := Matrix.elts m1 i j; let b : ℤ := Matrix.elts m1 i k; if Int.tmod i (2 : ℤ) = (0 : ℤ) then a ≤ b else b ≤ a)) → ¬(2 : ℤ) = (0 : ℤ) ∧ ((0 : ℤ) ≤ tid ∧ tid < Matrix.rows m1) ∧ (∀(m2 : Matrix.matrix ℤ), Matrix.rows m2 = Matrix.rows m1 ∧ Matrix.columns m2 = Matrix.columns m1 → (∀(j : ℤ) (k : ℤ), (0 : ℤ) ≤ j ∧ j < Matrix.rows m2 ∧ ((0 : ℤ) ≤ k ∧ k < Matrix.columns m2) ∧ ¬j = tid → Matrix.elts m2 j k = Matrix.elts m1 j k) ∧ (∀(j : ℤ) (k : ℤ), (0 : ℤ) ≤ j ∧ j ≤ k ∧ k < Matrix.columns m2 → (let a : ℤ := Matrix.elts m2 tid j; let b : ℤ := Matrix.elts m2 tid k; if Int.tmod tid (2 : ℤ) = (0 : ℤ) then a ≤ b else b ≤ a)) ∧ MapPermut.permut (Matrix.elts m2 tid) (Matrix.elts m1 tid) (0 : ℤ) (Matrix.columns m2) → (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m2 → MapPermut.permut (Matrix.elts m2 i) (Matrix.elts m i) (0 : ℤ) (Matrix.columns m2)) ∧ (∀(i : ℤ) (j : ℤ) (k : ℤ), ((0 : ℤ) ≤ i ∧ i < tid + (1 : ℤ)) ∧ (0 : ℤ) ≤ j ∧ j ≤ k ∧ k < Matrix.columns m2 → (let a : ℤ := Matrix.elts m2 i j; let b : ℤ := Matrix.elts m2 i k; if Int.tmod i (2 : ℤ) = (0 : ℤ) then a ≤ b else b ≤ a)))) ∧ ((∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m1 → MapPermut.permut (Matrix.elts m1 i) (Matrix.elts m i) (0 : ℤ) (Matrix.columns m1)) ∧ (∀(i : ℤ) (j : ℤ) (k : ℤ), ((0 : ℤ) ≤ i ∧ i < o1 + (1 : ℤ)) ∧ (0 : ℤ) ≤ j ∧ j ≤ k ∧ k < Matrix.columns m1 → (let a : ℤ := Matrix.elts m1 i j; let b : ℤ := Matrix.elts m1 i k; if Int.tmod i (2 : ℤ) = (0 : ℤ) then a ≤ b else b ≤ a)) → (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m1 → MapPermut.permut (Matrix.elts m1 i) (Matrix.elts m i) (0 : ℤ) (Matrix.columns m1)) ∧ (∀(i : ℤ) (j : ℤ) (k : ℤ), ((0 : ℤ) ≤ i ∧ i < Matrix.rows m1) ∧ (0 : ℤ) ≤ j ∧ j ≤ k ∧ k < Matrix.columns m1 → (let a : ℤ := Matrix.elts m1 i j; let b : ℤ := Matrix.elts m1 i k; if Int.tmod i (2 : ℤ) = (0 : ℤ) then a ≤ b else b ≤ a))))) ∧ (o1 + (1 : ℤ) < (0 : ℤ) → (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Matrix.rows m → MapPermut.permut (Matrix.elts m i) (Matrix.elts m i) (0 : ℤ) (Matrix.columns m)) ∧ (∀(i : ℤ) (j : ℤ) (k : ℤ), ((0 : ℤ) ≤ i ∧ i < Matrix.rows m) ∧ (0 : ℤ) ≤ j ∧ j ≤ k ∧ k < Matrix.columns m → (let a : ℤ := Matrix.elts m i j; let b : ℤ := Matrix.elts m i k; if Int.tmod i (2 : ℤ) = (0 : ℤ) then a ≤ b else b ≤ a)))
  := sorry
end verifythis_2021_shearsort_ShearSort_sort_all_rowsqtvc
