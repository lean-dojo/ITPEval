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
namespace warshall_algorithm_WarshallAlgorithm_transitive_closureqtvc
inductive path : Matrix.matrix Bool -> ℤ -> ℤ -> ℤ -> Prop where
 | Path_empty (m : Matrix.matrix Bool) (i : ℤ) (j : ℤ) (k : ℤ) : Matrix.elts m i j = true → path m i j k
 | Path_cons (x : ℤ) (k : ℤ) (m : Matrix.matrix Bool) (i : ℤ) (j : ℤ) : (0 : ℤ) ≤ x → x < k → path m i x k → path m x j k → path m i j k
theorem transitive_closure'vc (m : Matrix.matrix Bool) (t : Matrix.matrix Bool) (fact0 : Matrix.rows m = Matrix.columns m) (fact1 : Matrix.rows t = Matrix.rows m) (fact2 : Matrix.columns t = Matrix.columns m) (fact3 : ∀(r : ℤ), (0 : ℤ) ≤ r ∧ r < Matrix.rows t → (∀(c : ℤ), (0 : ℤ) ≤ c ∧ c < Matrix.columns t → Matrix.elts t r c = Matrix.elts m r c)) : let n : ℤ := Matrix.rows m; let o1 : ℤ := n - (1 : ℤ); ((0 : ℤ) ≤ o1 + (1 : ℤ) → (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t x y = true) = path m x y (0 : ℤ)) ∧ (∀(t1 : Matrix.matrix Bool), Matrix.rows t1 = Matrix.rows t ∧ Matrix.columns t1 = Matrix.columns t → (∀(k : ℤ), ((0 : ℤ) ≤ k ∧ k ≤ o1) ∧ (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t1 x y = true) = path m x y k) → (let o2 : ℤ := n - (1 : ℤ); ((0 : ℤ) ≤ o2 + (1 : ℤ) → (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t1 x y = true) = (if x < (0 : ℤ) then path m x y (k + (1 : ℤ)) else path m x y k)) ∧ (∀(t2 : Matrix.matrix Bool), Matrix.rows t2 = Matrix.rows t1 ∧ Matrix.columns t2 = Matrix.columns t1 → (∀(i : ℤ), ((0 : ℤ) ≤ i ∧ i ≤ o2) ∧ (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t2 x y = true) = (if x < i then path m x y (k + (1 : ℤ)) else path m x y k)) → (let o3 : ℤ := n - (1 : ℤ); ((0 : ℤ) ≤ o3 + (1 : ℤ) → (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t2 x y = true) = (if x < i ∨ x = i ∧ y < (0 : ℤ) then path m x y (k + (1 : ℤ)) else path m x y k)) ∧ (∀(t3 : Matrix.matrix Bool), Matrix.rows t3 = Matrix.rows t2 ∧ Matrix.columns t3 = Matrix.columns t2 → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j ≤ o3) ∧ (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t3 x y = true) = (if x < i ∨ x = i ∧ y < j then path m x y (k + (1 : ℤ)) else path m x y k)) → Matrix.valid_index t3 i j ∧ (let o4 : Bool := Matrix.elts t3 i j; (¬o4 = true → Matrix.valid_index t3 i k ∧ (Matrix.elts t3 i k = true → Matrix.valid_index t3 k j)) ∧ (∀(o5 : Bool), (if o4 = true then o5 = true else if Matrix.elts t3 i k = true then o5 = Matrix.elts t3 k j else o5 = false) → Matrix.valid_index t3 i j ∧ (∀(t4 : Matrix.matrix Bool), Matrix.rows t4 = Matrix.rows t3 ∧ Matrix.columns t4 = Matrix.columns t3 → Matrix.elts t4 = Function.update (Matrix.elts t3) i (Function.update (Matrix.elts t3 i) j o5) → (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t4 x y = true) = (if x < i ∨ x = i ∧ y < j + (1 : ℤ) then path m x y (k + (1 : ℤ)) else path m x y k)))))) ∧ ((∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t3 x y = true) = (if x < i ∨ x = i ∧ y < o3 + (1 : ℤ) then path m x y (k + (1 : ℤ)) else path m x y k)) → (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t3 x y = true) = (if x < i + (1 : ℤ) then path m x y (k + (1 : ℤ)) else path m x y k))))) ∧ (o3 + (1 : ℤ) < (0 : ℤ) → (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t2 x y = true) = (if x < i + (1 : ℤ) then path m x y (k + (1 : ℤ)) else path m x y k))))) ∧ ((∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t2 x y = true) = (if x < o2 + (1 : ℤ) then path m x y (k + (1 : ℤ)) else path m x y k)) → (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t2 x y = true) = path m x y (k + (1 : ℤ)))))) ∧ (o2 + (1 : ℤ) < (0 : ℤ) → (∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t1 x y = true) = path m x y (k + (1 : ℤ)))))) ∧ ((∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n → (0 : ℤ) ≤ y ∧ y < n → (Matrix.elts t1 x y = true) = path m x y (o1 + (1 : ℤ))) → (let n1 : ℤ := Matrix.rows m; ∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n1 → (0 : ℤ) ≤ y ∧ y < n1 → (Matrix.elts t1 x y = true) = path m x y n1)))) ∧ (o1 + (1 : ℤ) < (0 : ℤ) → (let n1 : ℤ := Matrix.rows m; ∀(x : ℤ) (y : ℤ), (0 : ℤ) ≤ x ∧ x < n1 → (0 : ℤ) ≤ y ∧ y < n1 → (Matrix.elts t x y = true) = path m x y n1))
  := sorry
end warshall_algorithm_WarshallAlgorithm_transitive_closureqtvc
