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
namespace schorr_waite_SchorrWaite_schorr_waiteqtvc
axiom loc : Type
axiom inhabited_axiom_loc : Inhabited loc
attribute [instance] inhabited_axiom_loc
axiom null : loc
axiom stacknodes : Type
axiom inhabited_axiom_stacknodes : Inhabited stacknodes
attribute [instance] inhabited_axiom_stacknodes
noncomputable def not_in_stack (n : loc) (s : List loc) := ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length s) → ¬n = s[Int.toNat i]!
noncomputable def last (s : List loc) := s[Int.toNat (Int.ofNat (List.length s) - (1 : ℤ))]!
noncomputable def distinct (s : List loc) := ∀(i : ℤ) (j : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length s) → (0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length s) → ¬i = j → ¬s[Int.toNat i]! = s[Int.toNat j]!
noncomputable def edge (x : loc) (y : loc) (left1 : loc -> loc) (right1 : loc -> loc) := ¬x = null ∧ (left1 x = y ∨ right1 x = y)
inductive path : (loc -> loc) -> (loc -> loc) -> loc -> loc -> List loc -> Prop where
 | path_nil (l : loc -> loc) (r : loc -> loc) (x : loc) : path l r x x ([] : List loc)
 | path_cons (x : loc) (z : loc) (l : loc -> loc) (r : loc -> loc) (y : loc) (p : List loc) : edge x z l r → path l r z y p → path l r x y (List.cons x p)
noncomputable def reachable (left1 : loc -> loc) (right1 : loc -> loc) (x : loc) (y : loc) := ∃(p : List loc), path left1 right1 x y p
theorem schorr_waite'vc (root : loc) (graph : Finset loc) (left1 : loc -> loc) (right1 : loc -> loc) (m : loc -> Bool) (c : loc -> Bool) (path_from_root : loc -> List loc) (fact0 : ¬root = null) (fact1 : root ∈ graph) (fact2 : ∀(n : loc), n ∈ graph → ¬n = null ∧ (left1 n = null ∨ left1 n ∈ graph) ∧ (right1 n = null ∨ right1 n ∈ graph)) (fact3 : ∀(x : loc), x ∈ graph → ¬m x = true) : ¬root = null ∧ (∀(n : loc), n ∈ graph → not_in_stack n ([] : List loc) ∨ (∃(i : ℤ), ([] : List loc)[Int.toNat i]! = n)) ∧ not_in_stack null ([] : List loc) ∧ Int.ofNat (List.length ([] : List loc)) = (0 : ℤ) ∧ (¬Int.ofNat (List.length ([] : List loc)) = (0 : ℤ) → ([] : List loc)[(0 : ℕ)]! = null) ∧ (∀(n : loc), n ∈ graph → ¬m n = true → n ∈ graph) ∧ (∀(n : loc), n ∈ graph → ¬c n = true → n ∈ graph) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length ([] : List loc)) → ([] : List loc)[Int.toNat i]! ∈ graph) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length ([] : List loc)) - (1 : ℤ) → (let p1 : loc := ([] : List loc)[Int.toNat i]!; let p2 : loc := ([] : List loc)[Int.toNat (i + (1 : ℤ))]!; (c p2 = true → right1 p2 = p1) ∧ (¬c p2 = true → left1 p2 = p1))) ∧ Function.update path_from_root root ([] : List loc) root = ([] : List loc) ∧ (¬Int.ofNat (List.length ([] : List loc)) = (0 : ℤ) → (let first : loc := last ([] : List loc); if c first = true then right1 first = null else left1 first = null)) ∧ (¬Int.ofNat (List.length ([] : List loc)) = (0 : ℤ) → last ([] : List loc) = root) ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length ([] : List loc)) - (1 : ℤ) → (if c (([] : List loc)[Int.toNat k]!) = true then right1 (([] : List loc)[Int.toNat k]!) = ([] : List loc)[Int.toNat (k + (1 : ℤ))]! else left1 (([] : List loc)[Int.toNat k]!) = ([] : List loc)[Int.toNat (k + (1 : ℤ))]!)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length ([] : List loc)) → m (([] : List loc)[Int.toNat i]!) = true) ∧ distinct ([] : List loc) ∧ (¬Int.ofNat (List.length ([] : List loc)) = (0 : ℤ) → (if c null = true then right1 null = root else left1 null = root)) ∧ (∀(k : ℤ), (0 : ℤ) < k ∧ k < Int.ofNat (List.length ([] : List loc)) → (let n : loc := ([] : List loc)[Int.toNat k]!; if c n = true then ([] : List loc)[Int.toNat (k - (1 : ℤ))]! = right1 n else ([] : List loc)[Int.toNat (k - (1 : ℤ))]! = left1 n)) ∧ (∀(n : loc), n ∈ graph → m n = true → reachable left1 right1 root n) ∧ (∀(n : loc), n ∈ graph → m n = true → path left1 right1 root n (Function.update path_from_root root ([] : List loc) n)) ∧ (∀(n : loc), n ∈ graph → ¬n = null → m n = true → not_in_stack n ([] : List loc) → (¬left1 n = null → m (left1 n) = true) ∧ (¬right1 n = null → m (right1 n) = true)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length ([] : List loc)) → (let n : loc := ([] : List loc)[Int.toNat i]!; c n = true → (¬left1 n = null → m (left1 n) = true) ∧ (¬right1 n = null → m (right1 n) = true))) ∧ (∀(c_false_nodes : Finset loc) (unmarked_nodes : Finset loc) (pth : List loc) (stackNodes : List loc) (p : loc) (t : loc) (path_from_root1 : loc -> List loc) (right2 : loc -> loc) (left2 : loc -> loc) (c1 : loc -> Bool) (m1 : loc -> Bool), (∀(n : loc), n ∈ graph → not_in_stack n stackNodes ∨ (∃(i : ℤ), stackNodes[Int.toNat i]! = n)) ∧ not_in_stack null stackNodes ∧ (Int.ofNat (List.length stackNodes) = (0 : ℤ)) = (p = null) ∧ (¬p = null → p ∈ graph) ∧ (¬Int.ofNat (List.length stackNodes) = (0 : ℤ) → stackNodes[(0 : ℕ)]! = p) ∧ (∀(n : loc), n ∈ graph → ¬m1 n = true → n ∈ unmarked_nodes) ∧ (∀(n : loc), n ∈ graph → ¬c1 n = true → n ∈ c_false_nodes) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length stackNodes) → stackNodes[Int.toNat i]! ∈ graph) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length stackNodes) - (1 : ℤ) → (let p1 : loc := stackNodes[Int.toNat i]!; let p2 : loc := stackNodes[Int.toNat (i + (1 : ℤ))]!; (c1 p2 = true → left1 p2 = left2 p2 ∧ right1 p2 = p1) ∧ (¬c1 p2 = true → left1 p2 = p1 ∧ right1 p2 = right2 p2))) ∧ path_from_root1 root = ([] : List loc) ∧ (∀(n : loc), n ∈ graph → not_in_stack n stackNodes → left2 n = left1 n ∧ right2 n = right1 n) ∧ (¬Int.ofNat (List.length stackNodes) = (0 : ℤ) → (let first : loc := last stackNodes; if c1 first = true then right2 first = null else left2 first = null)) ∧ (¬Int.ofNat (List.length stackNodes) = (0 : ℤ) → last stackNodes = root) ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length stackNodes) - (1 : ℤ) → (if c1 (stackNodes[Int.toNat k]!) = true then right2 (stackNodes[Int.toNat k]!) = stackNodes[Int.toNat (k + (1 : ℤ))]! else left2 (stackNodes[Int.toNat k]!) = stackNodes[Int.toNat (k + (1 : ℤ))]!)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length stackNodes) → m1 (stackNodes[Int.toNat i]!) = true) ∧ distinct stackNodes ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length stackNodes) → (let n : loc := stackNodes[Int.toNat i]!; if c1 n = true then left2 n = left1 n else right2 n = right1 n)) ∧ (¬Int.ofNat (List.length stackNodes) = (0 : ℤ) → (if c1 p = true then right1 p = t else left1 p = t)) ∧ (∀(k : ℤ), (0 : ℤ) < k ∧ k < Int.ofNat (List.length stackNodes) → (let n : loc := stackNodes[Int.toNat k]!; if c1 n = true then stackNodes[Int.toNat (k - (1 : ℤ))]! = right1 n else stackNodes[Int.toNat (k - (1 : ℤ))]! = left1 n)) ∧ (¬p = null → path left1 right1 root p pth) ∧ (∀(n : loc), n ∈ graph → m1 n = true → reachable left1 right1 root n) ∧ (p = null → t = root) ∧ (∀(n : loc), n ∈ graph → m1 n = true → path left1 right1 root n (path_from_root1 n)) ∧ (∀(n : loc), n ∈ graph → ¬n = null → m1 n = true → not_in_stack n stackNodes → (¬left2 n = null → m1 (left2 n) = true) ∧ (¬right2 n = null → m1 (right2 n) = true)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length stackNodes) → (let n : loc := stackNodes[Int.toNat i]!; c1 n = true → (¬left2 n = null → m1 (left2 n) = true) ∧ (¬right2 n = null → m1 (right2 n) = true))) → (∀(o1 : Bool), (if ¬p = null then o1 = true else if ¬t = null then o1 = (if m1 t = true then false else true) else o1 = false) → (if o1 = true then ∀(o2 : Bool), (if t = null then o2 = true else o2 = m1 t) → (if o2 = true then ¬p = null ∧ (if c1 p = true then (0 : ℤ) < Int.ofNat (List.length stackNodes) ∧ (let o3 : List loc := List.drop (1 : ℕ) stackNodes; (∀(n : loc), not_in_stack n stackNodes → not_in_stack n o3) → ¬p = null ∧ ¬p = null ∧ ((0 : ℤ) ≤ Int.ofNat (Finset.card unmarked_nodes) ∧ Finset.card unmarked_nodes < Finset.card unmarked_nodes ∨ (0 : ℤ) ≤ Int.ofNat (Finset.card c_false_nodes) ∧ Finset.card c_false_nodes < Finset.card c_false_nodes ∨ (0 : ℤ) ≤ Int.ofNat (List.length stackNodes) ∧ List.length o3 < List.length stackNodes) ∧ (∀(n : loc), n ∈ graph → not_in_stack n o3 ∨ (∃(i : ℤ), o3[Int.toNat i]! = n)) ∧ not_in_stack null o3 ∧ (Int.ofNat (List.length o3) = (0 : ℤ)) = (right2 p = null) ∧ (¬right2 p = null → right2 p ∈ graph) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → o3[(0 : ℕ)]! = right2 p) ∧ (∀(n : loc), n ∈ graph → ¬m1 n = true → n ∈ unmarked_nodes) ∧ (∀(n : loc), n ∈ graph → ¬c1 n = true → n ∈ c_false_nodes) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → o3[Int.toNat i]! ∈ graph) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) - (1 : ℤ) → (let p1 : loc := o3[Int.toNat i]!; let p2 : loc := o3[Int.toNat (i + (1 : ℤ))]!; (c1 p2 = true → left1 p2 = left2 p2 ∧ right1 p2 = p1) ∧ (¬c1 p2 = true → left1 p2 = p1 ∧ right1 p2 = Function.update right2 p t p2))) ∧ path_from_root1 root = ([] : List loc) ∧ (∀(n : loc), n ∈ graph → not_in_stack n o3 → left2 n = left1 n ∧ Function.update right2 p t n = right1 n) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → (let first : loc := last o3; if c1 first = true then Function.update right2 p t first = null else left2 first = null)) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → last o3 = root) ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length o3) - (1 : ℤ) → (if c1 (o3[Int.toNat k]!) = true then Function.update right2 p t (o3[Int.toNat k]!) = o3[Int.toNat (k + (1 : ℤ))]! else left2 (o3[Int.toNat k]!) = o3[Int.toNat (k + (1 : ℤ))]!)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → m1 (o3[Int.toNat i]!) = true) ∧ distinct o3 ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → (let n : loc := o3[Int.toNat i]!; if c1 n = true then left2 n = left1 n else Function.update right2 p t n = right1 n)) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → (if c1 (right2 p) = true then right1 (right2 p) = p else left1 (right2 p) = p)) ∧ (∀(k : ℤ), (0 : ℤ) < k ∧ k < Int.ofNat (List.length o3) → (let n : loc := o3[Int.toNat k]!; if c1 n = true then o3[Int.toNat (k - (1 : ℤ))]! = right1 n else o3[Int.toNat (k - (1 : ℤ))]! = left1 n)) ∧ (¬right2 p = null → path left1 right1 root (right2 p) (path_from_root1 (right2 p))) ∧ (∀(n : loc), n ∈ graph → m1 n = true → reachable left1 right1 root n) ∧ (right2 p = null → p = root) ∧ (∀(n : loc), n ∈ graph → m1 n = true → path left1 right1 root n (path_from_root1 n)) ∧ (∀(n : loc), n ∈ graph → ¬n = null → m1 n = true → not_in_stack n o3 → (¬left2 n = null → m1 (left2 n) = true) ∧ (¬Function.update right2 p t n = null → m1 (Function.update right2 p t n) = true)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → (let n : loc := o3[Int.toNat i]!; c1 n = true → (¬left2 n = null → m1 (left2 n) = true) ∧ (¬Function.update right2 p t n = null → m1 (Function.update right2 p t n) = true)))) else ¬p = null ∧ ¬p = null ∧ ¬p = null ∧ ¬p = null ∧ ¬p = null ∧ ((0 : ℤ) ≤ Int.ofNat (Finset.card unmarked_nodes) ∧ Finset.card unmarked_nodes < Finset.card unmarked_nodes ∨ (0 : ℤ) ≤ Int.ofNat (Finset.card c_false_nodes) ∧ Finset.card (Finset.erase c_false_nodes p) < Finset.card c_false_nodes ∨ Finset.card c_false_nodes = Finset.card (Finset.erase c_false_nodes p) ∧ (0 : ℤ) ≤ Int.ofNat (List.length stackNodes) ∧ List.length stackNodes < List.length stackNodes) ∧ (∀(n : loc), n ∈ graph → not_in_stack n stackNodes ∨ (∃(i : ℤ), stackNodes[Int.toNat i]! = n)) ∧ not_in_stack null stackNodes ∧ (Int.ofNat (List.length stackNodes) = (0 : ℤ)) = (p = null) ∧ (¬p = null → p ∈ graph) ∧ (¬Int.ofNat (List.length stackNodes) = (0 : ℤ) → stackNodes[(0 : ℕ)]! = p) ∧ (∀(n : loc), n ∈ graph → ¬m1 n = true → n ∈ unmarked_nodes) ∧ (∀(n : loc), n ∈ graph → ¬Function.update c1 p true n = true → n ∈ Finset.erase c_false_nodes p) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length stackNodes) → stackNodes[Int.toNat i]! ∈ graph) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length stackNodes) - (1 : ℤ) → (let p1 : loc := stackNodes[Int.toNat i]!; let p2 : loc := stackNodes[Int.toNat (i + (1 : ℤ))]!; (Function.update c1 p true p2 = true → left1 p2 = Function.update left2 p t p2 ∧ right1 p2 = p1) ∧ (¬Function.update c1 p true p2 = true → left1 p2 = p1 ∧ right1 p2 = Function.update right2 p (left2 p) p2))) ∧ path_from_root1 root = ([] : List loc) ∧ (∀(n : loc), n ∈ graph → not_in_stack n stackNodes → Function.update left2 p t n = left1 n ∧ Function.update right2 p (left2 p) n = right1 n) ∧ (¬Int.ofNat (List.length stackNodes) = (0 : ℤ) → (let first : loc := last stackNodes; if Function.update c1 p true first = true then Function.update right2 p (left2 p) first = null else Function.update left2 p t first = null)) ∧ (¬Int.ofNat (List.length stackNodes) = (0 : ℤ) → last stackNodes = root) ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length stackNodes) - (1 : ℤ) → (if Function.update c1 p true (stackNodes[Int.toNat k]!) = true then Function.update right2 p (left2 p) (stackNodes[Int.toNat k]!) = stackNodes[Int.toNat (k + (1 : ℤ))]! else Function.update left2 p t (stackNodes[Int.toNat k]!) = stackNodes[Int.toNat (k + (1 : ℤ))]!)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length stackNodes) → m1 (stackNodes[Int.toNat i]!) = true) ∧ distinct stackNodes ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length stackNodes) → (let n : loc := stackNodes[Int.toNat i]!; if Function.update c1 p true n = true then Function.update left2 p t n = left1 n else Function.update right2 p (left2 p) n = right1 n)) ∧ (¬Int.ofNat (List.length stackNodes) = (0 : ℤ) → (if Function.update c1 p true p = true then right1 p = right2 p else left1 p = right2 p)) ∧ (∀(k : ℤ), (0 : ℤ) < k ∧ k < Int.ofNat (List.length stackNodes) → (let n : loc := stackNodes[Int.toNat k]!; if Function.update c1 p true n = true then stackNodes[Int.toNat (k - (1 : ℤ))]! = right1 n else stackNodes[Int.toNat (k - (1 : ℤ))]! = left1 n)) ∧ (¬p = null → path left1 right1 root p pth) ∧ (∀(n : loc), n ∈ graph → m1 n = true → reachable left1 right1 root n) ∧ (p = null → right2 p = root) ∧ (∀(n : loc), n ∈ graph → m1 n = true → path left1 right1 root n (path_from_root1 n)) ∧ (∀(n : loc), n ∈ graph → ¬n = null → m1 n = true → not_in_stack n stackNodes → (¬Function.update left2 p t n = null → m1 (Function.update left2 p t n) = true) ∧ (¬Function.update right2 p (left2 p) n = null → m1 (Function.update right2 p (left2 p) n) = true)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length stackNodes) → (let n : loc := stackNodes[Int.toNat i]!; Function.update c1 p true n = true → (¬Function.update left2 p t n = null → m1 (Function.update left2 p t n) = true) ∧ (¬Function.update right2 p (left2 p) n = null → m1 (Function.update right2 p (left2 p) n) = true)))) else let o3 : List loc := List.cons t stackNodes; Int.ofNat (List.length o3) = (1 : ℤ) + Int.ofNat (List.length stackNodes) ∧ o3[(0 : ℕ)]! = t ∧ (∀(i : ℤ), (0 : ℤ) < i ∧ i ≤ Int.ofNat (List.length stackNodes) → o3[Int.toNat i]! = stackNodes[Int.toNat (i - (1 : ℤ))]!) → ¬t = null ∧ ¬t = null ∧ ¬t = null ∧ (if ¬t = root then ¬t = null ∧ ¬t = null ∧ ((0 : ℤ) ≤ Int.ofNat (Finset.card unmarked_nodes) ∧ Finset.card (Finset.erase unmarked_nodes t) < Finset.card unmarked_nodes ∨ Finset.card unmarked_nodes = Finset.card (Finset.erase unmarked_nodes t) ∧ ((0 : ℤ) ≤ Int.ofNat (Finset.card c_false_nodes) ∧ Finset.card (insert t c_false_nodes) < Finset.card c_false_nodes ∨ Finset.card c_false_nodes = Finset.card (insert t c_false_nodes) ∧ (0 : ℤ) ≤ Int.ofNat (List.length stackNodes) ∧ List.length o3 < List.length stackNodes)) ∧ (∀(n : loc), n ∈ graph → not_in_stack n o3 ∨ (∃(i : ℤ), o3[Int.toNat i]! = n)) ∧ not_in_stack null o3 ∧ (Int.ofNat (List.length o3) = (0 : ℤ)) = (t = null) ∧ (¬t = null → t ∈ graph) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → o3[(0 : ℕ)]! = t) ∧ (∀(n : loc), n ∈ graph → ¬Function.update m1 t true n = true → n ∈ Finset.erase unmarked_nodes t) ∧ (∀(n : loc), n ∈ graph → ¬Function.update c1 t false n = true → n ∈ insert t c_false_nodes) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → o3[Int.toNat i]! ∈ graph) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) - (1 : ℤ) → (let p1 : loc := o3[Int.toNat i]!; let p2 : loc := o3[Int.toNat (i + (1 : ℤ))]!; (Function.update c1 t false p2 = true → left1 p2 = Function.update left2 t p p2 ∧ right1 p2 = p1) ∧ (¬Function.update c1 t false p2 = true → left1 p2 = p1 ∧ right1 p2 = right2 p2))) ∧ Function.update path_from_root1 t (pth ++ List.cons p ([] : List loc)) root = ([] : List loc) ∧ (∀(n : loc), n ∈ graph → not_in_stack n o3 → Function.update left2 t p n = left1 n ∧ right2 n = right1 n) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → (let first : loc := last o3; if Function.update c1 t false first = true then right2 first = null else Function.update left2 t p first = null)) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → last o3 = root) ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length o3) - (1 : ℤ) → (if Function.update c1 t false (o3[Int.toNat k]!) = true then right2 (o3[Int.toNat k]!) = o3[Int.toNat (k + (1 : ℤ))]! else Function.update left2 t p (o3[Int.toNat k]!) = o3[Int.toNat (k + (1 : ℤ))]!)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → Function.update m1 t true (o3[Int.toNat i]!) = true) ∧ distinct o3 ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → (let n : loc := o3[Int.toNat i]!; if Function.update c1 t false n = true then Function.update left2 t p n = left1 n else right2 n = right1 n)) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → (if Function.update c1 t false t = true then right1 t = left2 t else left1 t = left2 t)) ∧ (∀(k : ℤ), (0 : ℤ) < k ∧ k < Int.ofNat (List.length o3) → (let n : loc := o3[Int.toNat k]!; if Function.update c1 t false n = true then o3[Int.toNat (k - (1 : ℤ))]! = right1 n else o3[Int.toNat (k - (1 : ℤ))]! = left1 n)) ∧ (¬t = null → path left1 right1 root t (pth ++ List.cons p ([] : List loc))) ∧ (∀(n : loc), n ∈ graph → Function.update m1 t true n = true → reachable left1 right1 root n) ∧ (t = null → left2 t = root) ∧ (∀(n : loc), n ∈ graph → Function.update m1 t true n = true → path left1 right1 root n (Function.update path_from_root1 t (pth ++ List.cons p ([] : List loc)) n)) ∧ (∀(n : loc), n ∈ graph → ¬n = null → Function.update m1 t true n = true → not_in_stack n o3 → (¬Function.update left2 t p n = null → Function.update m1 t true (Function.update left2 t p n) = true) ∧ (¬right2 n = null → Function.update m1 t true (right2 n) = true)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → (let n : loc := o3[Int.toNat i]!; Function.update c1 t false n = true → (¬Function.update left2 t p n = null → Function.update m1 t true (Function.update left2 t p n) = true) ∧ (¬right2 n = null → Function.update m1 t true (right2 n) = true))) else ¬t = null ∧ ¬t = null ∧ ((0 : ℤ) ≤ Int.ofNat (Finset.card unmarked_nodes) ∧ Finset.card (Finset.erase unmarked_nodes t) < Finset.card unmarked_nodes ∨ Finset.card unmarked_nodes = Finset.card (Finset.erase unmarked_nodes t) ∧ ((0 : ℤ) ≤ Int.ofNat (Finset.card c_false_nodes) ∧ Finset.card (insert t c_false_nodes) < Finset.card c_false_nodes ∨ Finset.card c_false_nodes = Finset.card (insert t c_false_nodes) ∧ (0 : ℤ) ≤ Int.ofNat (List.length stackNodes) ∧ List.length o3 < List.length stackNodes)) ∧ (∀(n : loc), n ∈ graph → not_in_stack n o3 ∨ (∃(i : ℤ), o3[Int.toNat i]! = n)) ∧ not_in_stack null o3 ∧ (Int.ofNat (List.length o3) = (0 : ℤ)) = (t = null) ∧ (¬t = null → t ∈ graph) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → o3[(0 : ℕ)]! = t) ∧ (∀(n : loc), n ∈ graph → ¬Function.update m1 t true n = true → n ∈ Finset.erase unmarked_nodes t) ∧ (∀(n : loc), n ∈ graph → ¬Function.update c1 t false n = true → n ∈ insert t c_false_nodes) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → o3[Int.toNat i]! ∈ graph) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) - (1 : ℤ) → (let p1 : loc := o3[Int.toNat i]!; let p2 : loc := o3[Int.toNat (i + (1 : ℤ))]!; (Function.update c1 t false p2 = true → left1 p2 = Function.update left2 t p p2 ∧ right1 p2 = p1) ∧ (¬Function.update c1 t false p2 = true → left1 p2 = p1 ∧ right1 p2 = right2 p2))) ∧ Function.update path_from_root1 t ([] : List loc) root = ([] : List loc) ∧ (∀(n : loc), n ∈ graph → not_in_stack n o3 → Function.update left2 t p n = left1 n ∧ right2 n = right1 n) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → (let first : loc := last o3; if Function.update c1 t false first = true then right2 first = null else Function.update left2 t p first = null)) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → last o3 = root) ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < Int.ofNat (List.length o3) - (1 : ℤ) → (if Function.update c1 t false (o3[Int.toNat k]!) = true then right2 (o3[Int.toNat k]!) = o3[Int.toNat (k + (1 : ℤ))]! else Function.update left2 t p (o3[Int.toNat k]!) = o3[Int.toNat (k + (1 : ℤ))]!)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → Function.update m1 t true (o3[Int.toNat i]!) = true) ∧ distinct o3 ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → (let n : loc := o3[Int.toNat i]!; if Function.update c1 t false n = true then Function.update left2 t p n = left1 n else right2 n = right1 n)) ∧ (¬Int.ofNat (List.length o3) = (0 : ℤ) → (if Function.update c1 t false t = true then right1 t = left2 t else left1 t = left2 t)) ∧ (∀(k : ℤ), (0 : ℤ) < k ∧ k < Int.ofNat (List.length o3) → (let n : loc := o3[Int.toNat k]!; if Function.update c1 t false n = true then o3[Int.toNat (k - (1 : ℤ))]! = right1 n else o3[Int.toNat (k - (1 : ℤ))]! = left1 n)) ∧ (¬t = null → path left1 right1 root t ([] : List loc)) ∧ (∀(n : loc), n ∈ graph → Function.update m1 t true n = true → reachable left1 right1 root n) ∧ (t = null → left2 t = root) ∧ (∀(n : loc), n ∈ graph → Function.update m1 t true n = true → path left1 right1 root n (Function.update path_from_root1 t ([] : List loc) n)) ∧ (∀(n : loc), n ∈ graph → ¬n = null → Function.update m1 t true n = true → not_in_stack n o3 → (¬Function.update left2 t p n = null → Function.update m1 t true (Function.update left2 t p n) = true) ∧ (¬right2 n = null → Function.update m1 t true (right2 n) = true)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length o3) → (let n : loc := o3[Int.toNat i]!; Function.update c1 t false n = true → (¬Function.update left2 t p n = null → Function.update m1 t true (Function.update left2 t p n) = true) ∧ (¬right2 n = null → Function.update m1 t true (right2 n) = true))))) else (∀(n : loc), n ∈ graph → left1 n = left2 n ∧ right1 n = right2 n) ∧ (∀(n : loc), n ∈ graph → m1 n = true → reachable left1 right1 root n) ∧ m1 root = true ∧ (∀(n : loc), n ∈ graph → m1 n = true → (∀(ch : loc), edge n ch left2 right2 → ¬ch = null → m1 ch = true)))))
  := sorry
end schorr_waite_SchorrWaite_schorr_waiteqtvc
