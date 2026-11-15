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
namespace Path
axiom state : Type
axiom inhabited_axiom_state : Inhabited state
attribute [instance] inhabited_axiom_state
axiom moves : state -> List state
axiom start : state
axiom success : state -> Prop
inductive path : state -> state -> ℤ -> Prop where
 | Path0 (s : state) : path s s (0 : ℤ)
 | Path1 (i : ℤ) (s : state) : (0 : ℤ) ≤ i → i < Int.ofNat (List.length (moves s)) → path s ((moves s)[Int.toNat i]!) (1 : ℤ)
 | Patht (s : state) (t : state) (n : ℤ) (u : state) (m : ℤ) : path s t n → path t u m → path s u (n + m)
noncomputable def move (s : state) (t : state) := ∃(i : ℤ), ((0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length (moves s))) ∧ t = (moves s)[Int.toNat i]!
inductive outcome where
  | NoSolution : outcome
  | Solution : state -> ℤ -> outcome
axiom inhabited_axiom_outcome : Inhabited outcome
attribute [instance] inhabited_axiom_outcome
end Path
namespace search_Bfs_bfsqtvc
theorem bfs'vc : let o1 : List Path.state := ([] : List Path.state); let o2 : Path.state := Path.start; let o3 : List Path.state := List.cons o2 o1; Int.ofNat (List.length o3) = (1 : ℤ) + Int.ofNat (List.length o1) ∧ o3[(0 : ℕ)]! = o2 ∧ (∀(i : ℤ), (0 : ℤ) < i ∧ i ≤ Int.ofNat (List.length o1) → o3[Int.toNat i]! = o1[Int.toNat (i - (1 : ℤ))]!) → ((0 : ℤ) ≤ (0 : ℤ) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → Path.path Path.start (o3[Int.toNat i]!) (0 : ℤ)) ∧ (∀(t : Path.state), Path.path Path.start t (0 : ℤ) → t ∈ o3) ∧ (∀(t : Path.state) (n : ℤ), Path.path Path.start t n → Path.success t → (0 : ℤ) ≤ n)) ∧ (∀(p : ℤ) (cur : List Path.state), (0 : ℤ) ≤ p ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length cur) → Path.path Path.start (cur[Int.toNat i]!) p) ∧ (∀(t : Path.state), Path.path Path.start t p → t ∈ cur) ∧ (∀(t : Path.state) (n : ℤ), Path.path Path.start t n → Path.success t → p ≤ n) → (if (0 : ℤ) < Int.ofNat (List.length cur) then let o4 : ℤ := Int.ofNat (List.length cur) - (1 : ℤ); ((0 : ℤ) ≤ o4 + (1 : ℤ) → ((∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < Int.ofNat (List.length ([] : List Path.state)) → (∃(j : ℤ), ((0 : ℤ) ≤ j ∧ j < (0 : ℤ)) ∧ Path.move (cur[Int.toNat j]!) (([] : List Path.state)[Int.toNat l]!))) ∧ (∀(j : ℤ) (k : ℤ), (0 : ℤ) ≤ j ∧ j < (0 : ℤ) → (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length (Path.moves (cur[Int.toNat j]!))) → (Path.moves (cur[Int.toNat j]!))[Int.toNat k]! ∈ ([] : List Path.state)) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < (0 : ℤ) → ¬Path.success (cur[Int.toNat j]!))) ∧ (∀(nxt : List Path.state), (∀(i : ℤ), ((0 : ℤ) ≤ i ∧ i ≤ o4) ∧ (∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < Int.ofNat (List.length nxt) → (∃(j : ℤ), ((0 : ℤ) ≤ j ∧ j < i) ∧ Path.move (cur[Int.toNat j]!) (nxt[Int.toNat l]!))) ∧ (∀(j : ℤ) (k : ℤ), (0 : ℤ) ≤ j ∧ j < i → (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length (Path.moves (cur[Int.toNat j]!))) → (Path.moves (cur[Int.toNat j]!))[Int.toNat k]! ∈ nxt) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < i → ¬Path.success (cur[Int.toNat j]!)) → (let s : Path.state := cur[Int.toNat i]!; if Path.success s then Path.path Path.start s p else let o5 : List Path.state := Path.moves s; let o6 : List Path.state := o5 ++ nxt; Int.ofNat (List.length o6) = Int.ofNat (List.length o5) + Int.ofNat (List.length nxt) ∧ (∀(i1 : ℤ), (0 : ℤ) ≤ i1 ∧ i1 < Int.ofNat (List.length o5) → o6[Int.toNat i1]! = o5[Int.toNat i1]!) ∧ (∀(i1 : ℤ), Int.ofNat (List.length o5) ≤ i1 ∧ i1 < Int.ofNat (List.length o6) → o6[Int.toNat i1]! = nxt[Int.toNat (i1 - Int.ofNat (List.length o5))]!) → (∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < Int.ofNat (List.length o6) → (∃(j : ℤ), ((0 : ℤ) ≤ j ∧ j < i + (1 : ℤ)) ∧ Path.move (cur[Int.toNat j]!) (o6[Int.toNat l]!))) ∧ (∀(j : ℤ) (k : ℤ), (0 : ℤ) ≤ j ∧ j < i + (1 : ℤ) → (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length (Path.moves (cur[Int.toNat j]!))) → (Path.moves (cur[Int.toNat j]!))[Int.toNat k]! ∈ o6) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < i + (1 : ℤ) → ¬Path.success (cur[Int.toNat j]!)))) ∧ ((∀(l : ℤ), (0 : ℤ) ≤ l ∧ l < Int.ofNat (List.length nxt) → (∃(j : ℤ), ((0 : ℤ) ≤ j ∧ j < o4 + (1 : ℤ)) ∧ Path.move (cur[Int.toNat j]!) (nxt[Int.toNat l]!))) ∧ (∀(j : ℤ) (k : ℤ), (0 : ℤ) ≤ j ∧ j < o4 + (1 : ℤ) → (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length (Path.moves (cur[Int.toNat j]!))) → (Path.moves (cur[Int.toNat j]!))[Int.toNat k]! ∈ nxt) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < o4 + (1 : ℤ) → ¬Path.success (cur[Int.toNat j]!)) → (0 : ℤ) ≤ p + (1 : ℤ) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length nxt) → Path.path Path.start (nxt[Int.toNat i]!) (p + (1 : ℤ))) ∧ (∀(t : Path.state), Path.path Path.start t (p + (1 : ℤ)) → t ∈ nxt) ∧ (∀(t : Path.state) (n : ℤ), Path.path Path.start t n → Path.success t → p + (1 : ℤ) ≤ n)))) ∧ (o4 + (1 : ℤ) < (0 : ℤ) → (0 : ℤ) ≤ p + (1 : ℤ) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length ([] : List Path.state)) → Path.path Path.start (([] : List Path.state)[Int.toNat i]!) (p + (1 : ℤ))) ∧ (∀(t : Path.state), Path.path Path.start t (p + (1 : ℤ)) → t ∈ ([] : List Path.state)) ∧ (∀(t : Path.state) (n : ℤ), Path.path Path.start t n → Path.success t → p + (1 : ℤ) ≤ n)) else ∀(t : Path.state) (n : ℤ), Path.success t → ¬Path.path Path.start t n))
  := sorry
end search_Bfs_bfsqtvc
