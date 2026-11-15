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
namespace Const
axiom const :  {β : Type} -> [Inhabited β] ->  {α : Type} -> [Inhabited α] -> β -> α -> β
axiom const'def {β : Type} {α : Type} [Inhabited β] [Inhabited α] (v : β) (x : α) : (const : β -> α -> β) v x = v
end Const
namespace Memory
axiom loc : Type
axiom inhabited_axiom_loc : Inhabited loc
attribute [instance] inhabited_axiom_loc
axiom null : loc
inductive color where
  | White : color
  | Black : Option ℤ -> color
axiom inhabited_axiom_color : Inhabited color
attribute [instance] inhabited_axiom_color
axiom pmem : Type
axiom inhabited_axiom_pmem : Inhabited pmem
attribute [instance] inhabited_axiom_pmem
axiom memory : Type
axiom inhabited_axiom_memory : Inhabited memory
attribute [instance] inhabited_axiom_memory
axiom block_size : memory -> loc -> ℤ
axiom accessor : memory -> loc -> ℤ -> loc
axiom colors : memory -> loc -> color
end Memory
namespace GraphShape
noncomputable def black (c : Memory.color) := ¬c = Memory.color.White
noncomputable def edge (m : Memory.memory) (x : Memory.loc) (y : Memory.loc) := ¬x = Memory.null ∧ (∃(n : ℤ), ((0 : ℤ) ≤ n ∧ n < Memory.block_size m x) ∧ Memory.accessor m x n = y)
inductive path : Memory.memory -> Memory.loc -> Memory.loc -> Prop where
 | path_nil (m : Memory.memory) (x : Memory.loc) : path m x x
 | path_cons (m : Memory.memory) (x : Memory.loc) (y : Memory.loc) (z : Memory.loc) : edge m x y → path m y z → path m x z
noncomputable def well_colored_on (graph : Finset Memory.loc) (gray : Finset Memory.loc) (m : Memory.memory) (cl : Memory.loc -> Memory.color) := gray ⊆ graph ∧ (∀(x : Memory.loc) (y : Memory.loc), x ∈ graph ∧ edge m x y ∧ ¬y = Memory.null ∧ black (cl x) → x ∈ gray ∨ black (cl y)) ∧ (∀(x : Memory.loc), x ∈ gray → black (cl x))
noncomputable def unchanged (m1 : Memory.memory) (m2 : Memory.memory) := ∀(x : Memory.loc) (n : ℤ), ¬x = Memory.null ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size m1 x → Memory.accessor m2 x n = Memory.accessor m1 x n
end GraphShape
namespace schorr_waite_via_recursion_SchorrWaite_schorr_waiteqtvc
theorem schorr_waite'vc (root : Memory.loc) (graph : Finset Memory.loc) (memo : Memory.memory) (fact0 : root ∈ graph) (fact1 : ∀(l : Memory.loc) (n : ℤ), l ∈ graph ∧ ¬l = Memory.null ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo l → Memory.accessor memo l n ∈ graph) (fact2 : ∀(x : Memory.loc), x ∈ graph → ¬GraphShape.black (Memory.colors memo x)) : (∀(p : Memory.loc) (t : Memory.loc) (memo1 : Memory.memory), Memory.block_size memo1 = Memory.block_size memo → (¬p = Memory.null ∧ (t = Memory.null ∨ GraphShape.black (Memory.colors memo1 t)) → (match Memory.colors memo1 p with | Memory.color.Black (Option.some m) => (0 : ℤ) ≤ m ∧ m < Memory.block_size memo1 p | _ => False)) → (∀(o1 : Bool), (if p = Memory.null then if t = Memory.null then o1 = true else o1 = (if GraphShape.black (Memory.colors memo1 t) then true else false) else o1 = false) → (if o1 = true then p = Memory.null ∧ (t = Memory.null ∨ GraphShape.black (Memory.colors memo1 t)) else ∀(o2 : Bool), (if t = Memory.null then o2 = true else o2 = (if GraphShape.black (Memory.colors memo1 t) then true else false)) → (if o2 = true then ¬p = Memory.null ∧ (match Memory.colors memo1 p with | Memory.color.Black (Option.some m) => ¬p = Memory.null ∧ (let s : ℤ := Memory.block_size memo1 p; (0 : ℤ) ≤ s → (let n : ℤ := m + (1 : ℤ); if n = s then (¬p = Memory.null ∧ (0 : ℤ) ≤ m ∧ m < Memory.block_size memo1 p) ∧ (¬p = Memory.null ∧ (0 : ℤ) ≤ m ∧ m < Memory.block_size memo1 p) ∧ (∀(memo2 : Memory.memory), Memory.block_size memo2 = Memory.block_size memo1 ∧ Memory.colors memo2 = Memory.colors memo1 → Memory.accessor memo2 = Function.update (Memory.accessor memo1) p (Function.update (Memory.accessor memo1 p) m t) → (¬p = Memory.null ∨ ¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t)) ∧ (¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t) ∧ Memory.block_size memo1 t = (0 : ℤ) → Memory.colors memo2 = Function.update (Memory.colors memo1) t (Memory.color.Black Option.none) ∧ p = t ∧ Memory.accessor memo1 p m = p ∧ Memory.accessor memo2 = Memory.accessor memo1) ∧ (¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t) ∧ (0 : ℤ) < Memory.block_size memo1 t → Memory.colors memo2 = Function.update (Memory.colors memo1) t (Memory.color.Black (Option.some (0 : ℤ))) ∧ p = Memory.accessor memo1 t (0 : ℤ) ∧ Memory.accessor memo1 p m = t ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) t (Function.update (Memory.accessor memo1 t) (0 : ℤ) p)) ∧ (t = Memory.null ∨ GraphShape.black (Memory.colors memo1 t) → (match Memory.colors memo1 p with | Memory.color.Black (Option.some m1) => (let n1 : ℤ := m1 + (1 : ℤ); if n1 = Memory.block_size memo1 p then Memory.accessor memo1 p m = Memory.accessor memo1 p m1 ∧ Memory.colors memo2 = Memory.colors memo1 ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) p (Function.update (Memory.accessor memo1 p) m1 t) else Memory.accessor memo1 p m = p ∧ p = Memory.accessor memo1 p n1 ∧ Memory.colors memo2 = Function.update (Memory.colors memo1) p (Memory.color.Black (Option.some n1)) ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) p (Function.update (Function.update (Memory.accessor memo1 p) n1 (Memory.accessor memo1 p m1)) m1 t)) | _ => False))) else (¬p = Memory.null ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo1 p) ∧ (¬p = Memory.null ∧ (0 : ℤ) ≤ m ∧ m < Memory.block_size memo1 p) ∧ (¬p = Memory.null ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo1 p) ∧ (∀(memo2 : Memory.memory), Memory.block_size memo2 = Memory.block_size memo1 ∧ Memory.colors memo2 = Memory.colors memo1 → Memory.accessor memo2 = Function.update (Memory.accessor memo1) p (Function.update (Memory.accessor memo1 p) n (Memory.accessor memo1 p m)) → (¬p = Memory.null ∧ (0 : ℤ) ≤ m ∧ m < Memory.block_size memo2 p) ∧ (∀(memo3 : Memory.memory), Memory.block_size memo3 = Memory.block_size memo2 ∧ Memory.colors memo3 = Memory.colors memo2 → Memory.accessor memo3 = Function.update (Memory.accessor memo2) p (Function.update (Memory.accessor memo2 p) m t) → (¬p = Memory.null ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo3 p) ∧ (∀(memo4 : Memory.memory), Memory.block_size memo4 = Memory.block_size memo3 ∧ Memory.accessor memo4 = Memory.accessor memo3 → Memory.colors memo4 = Function.update (Memory.colors memo3) p (Memory.color.Black (Option.some n)) → (¬p = Memory.null ∨ ¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t)) ∧ (¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t) ∧ Memory.block_size memo1 t = (0 : ℤ) → Memory.colors memo4 = Function.update (Memory.colors memo1) t (Memory.color.Black Option.none) ∧ Memory.accessor memo1 p n = t ∧ Memory.accessor memo4 = Memory.accessor memo1) ∧ (¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t) ∧ (0 : ℤ) < Memory.block_size memo1 t → Memory.colors memo4 = Function.update (Memory.colors memo1) t (Memory.color.Black (Option.some (0 : ℤ))) ∧ Memory.accessor memo1 p n = Memory.accessor memo1 t (0 : ℤ) ∧ p = t ∧ Memory.accessor memo4 = Function.update (Memory.accessor memo1) t (Function.update (Memory.accessor memo1 t) (0 : ℤ) p)) ∧ (t = Memory.null ∨ GraphShape.black (Memory.colors memo1 t) → (match Memory.colors memo1 p with | Memory.color.Black (Option.some m1) => (let n1 : ℤ := m1 + (1 : ℤ); if n1 = Memory.block_size memo1 p then Memory.accessor memo1 p n = p ∧ p = Memory.accessor memo1 p m1 ∧ Memory.colors memo4 = Memory.colors memo1 ∧ Memory.accessor memo4 = Function.update (Memory.accessor memo1) p (Function.update (Memory.accessor memo1 p) m1 t) else Memory.accessor memo1 p n = Memory.accessor memo1 p n1 ∧ Memory.colors memo4 = Function.update (Memory.colors memo1) p (Memory.color.Black (Option.some n1)) ∧ Memory.accessor memo4 = Function.update (Memory.accessor memo1) p (Function.update (Function.update (Memory.accessor memo1 p) n1 (Memory.accessor memo1 p m1)) m1 t)) | _ => False))))))) | _ => False) else ¬t = Memory.null ∧ (let s : ℤ := Memory.block_size memo1 t; (0 : ℤ) ≤ s → (if s = (0 : ℤ) then (¬t = Memory.null ∧ Memory.block_size memo1 t = (0 : ℤ)) ∧ (∀(memo2 : Memory.memory), Memory.block_size memo2 = Memory.block_size memo1 ∧ Memory.accessor memo2 = Memory.accessor memo1 → Memory.colors memo2 = Function.update (Memory.colors memo1) t (Memory.color.Black Option.none) → (¬p = Memory.null ∨ ¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t)) ∧ (¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t) ∧ Memory.block_size memo1 t = (0 : ℤ) → Memory.colors memo2 = Function.update (Memory.colors memo1) t (Memory.color.Black Option.none) ∧ Memory.accessor memo2 = Memory.accessor memo1) ∧ (¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t) ∧ (0 : ℤ) < Memory.block_size memo1 t → Memory.colors memo2 = Function.update (Memory.colors memo1) t (Memory.color.Black (Option.some (0 : ℤ))) ∧ t = Memory.accessor memo1 t (0 : ℤ) ∧ p = t ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) t (Function.update (Memory.accessor memo1 t) (0 : ℤ) p)) ∧ (t = Memory.null ∨ GraphShape.black (Memory.colors memo1 t) → (match Memory.colors memo1 p with | Memory.color.Black (Option.some m) => (let n : ℤ := m + (1 : ℤ); if n = Memory.block_size memo1 p then t = p ∧ p = Memory.accessor memo1 p m ∧ Memory.colors memo2 = Memory.colors memo1 ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) p (Function.update (Memory.accessor memo1 p) m t) else t = Memory.accessor memo1 p n ∧ Memory.colors memo2 = Function.update (Memory.colors memo1) p (Memory.color.Black (Option.some n)) ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) p (Function.update (Function.update (Memory.accessor memo1 p) n (Memory.accessor memo1 p m)) m t)) | _ => False))) else (¬t = Memory.null ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) < Memory.block_size memo1 t) ∧ (¬t = Memory.null ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) < Memory.block_size memo1 t) ∧ (∀(memo2 : Memory.memory), Memory.block_size memo2 = Memory.block_size memo1 ∧ Memory.colors memo2 = Memory.colors memo1 → Memory.accessor memo2 = Function.update (Memory.accessor memo1) t (Function.update (Memory.accessor memo1 t) (0 : ℤ) p) → (¬t = Memory.null ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) < Memory.block_size memo2 t) ∧ (∀(memo3 : Memory.memory), Memory.block_size memo3 = Memory.block_size memo2 ∧ Memory.accessor memo3 = Memory.accessor memo2 → Memory.colors memo3 = Function.update (Memory.colors memo2) t (Memory.color.Black (Option.some (0 : ℤ))) → (¬p = Memory.null ∨ ¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t)) ∧ (¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t) ∧ Memory.block_size memo1 t = (0 : ℤ) → Memory.colors memo3 = Function.update (Memory.colors memo1) t (Memory.color.Black Option.none) ∧ Memory.accessor memo1 t (0 : ℤ) = t ∧ t = p ∧ Memory.accessor memo3 = Memory.accessor memo1) ∧ (¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t) ∧ (0 : ℤ) < Memory.block_size memo1 t → Memory.colors memo3 = Function.update (Memory.colors memo1) t (Memory.color.Black (Option.some (0 : ℤ))) ∧ Memory.accessor memo3 = Function.update (Memory.accessor memo1) t (Function.update (Memory.accessor memo1 t) (0 : ℤ) p)) ∧ (t = Memory.null ∨ GraphShape.black (Memory.colors memo1 t) → (match Memory.colors memo1 p with | Memory.color.Black (Option.some m) => (let n : ℤ := m + (1 : ℤ); if n = Memory.block_size memo1 p then Memory.accessor memo1 t (0 : ℤ) = p ∧ t = Memory.accessor memo1 p m ∧ Memory.colors memo3 = Memory.colors memo1 ∧ Memory.accessor memo3 = Function.update (Memory.accessor memo1) p (Function.update (Memory.accessor memo1 p) m t) else t = p ∧ Memory.accessor memo1 t (0 : ℤ) = Memory.accessor memo1 p n ∧ Memory.colors memo3 = Function.update (Memory.colors memo1) p (Memory.color.Black (Option.some n)) ∧ Memory.accessor memo3 = Function.update (Memory.accessor memo1) p (Function.update (Function.update (Memory.accessor memo1 p) n (Memory.accessor memo1 p m)) m t)) | _ => False)))))))))) ∧ (∀(p : Memory.loc) (t : Memory.loc) (memo1 : Memory.memory), Memory.block_size memo1 = Memory.block_size memo → (∀(gray : Finset Memory.loc), GraphShape.well_colored_on graph gray memo (Memory.colors memo1) ∧ t ∈ graph ∧ (∀(x : Memory.loc) (n : ℤ), ¬x = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 x) ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo1 x → Memory.accessor memo1 x n = Memory.accessor memo x n) → (∀(o1 : Bool), (if t = Memory.null then o1 = true else o1 = (if GraphShape.black (Memory.colors memo1 t) then true else false)) → (if o1 = true then GraphShape.unchanged memo1 memo1 ∧ GraphShape.well_colored_on graph gray memo (Memory.colors memo1) ∧ (GraphShape.black (Memory.colors memo1 t) ∨ t = Memory.null) else ¬t = Memory.null ∧ (let s : ℤ := Memory.block_size memo1 t; (0 : ℤ) ≤ s → (let g2 : Finset Memory.loc := insert t gray; (¬p = Memory.null ∧ (t = Memory.null ∨ GraphShape.black (Memory.colors memo1 t)) → (match Memory.colors memo1 p with | Memory.color.Black (Option.some m) => (0 : ℤ) ≤ m ∧ m < Memory.block_size memo1 p | _ => False)) ∧ (∀(p1 : Memory.loc) (t1 : Memory.loc) (memo2 : Memory.memory), Memory.block_size memo2 = Memory.block_size memo1 → ((¬p = Memory.null ∨ ¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t)) ∧ (¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t) ∧ Memory.block_size memo1 t = (0 : ℤ) → Memory.colors memo2 = Function.update (Memory.colors memo1) t (Memory.color.Black Option.none) ∧ t1 = t ∧ p1 = p ∧ Memory.accessor memo2 = Memory.accessor memo1) ∧ (¬t = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 t) ∧ (0 : ℤ) < Memory.block_size memo1 t → Memory.colors memo2 = Function.update (Memory.colors memo1) t (Memory.color.Black (Option.some (0 : ℤ))) ∧ t1 = Memory.accessor memo1 t (0 : ℤ) ∧ p1 = t ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) t (Function.update (Memory.accessor memo1 t) (0 : ℤ) p)) ∧ (t = Memory.null ∨ GraphShape.black (Memory.colors memo1 t) → (match Memory.colors memo1 p with | Memory.color.Black (Option.some m) => (let n : ℤ := m + (1 : ℤ); if n = Memory.block_size memo1 p then t1 = p ∧ p1 = Memory.accessor memo1 p m ∧ Memory.colors memo2 = Memory.colors memo1 ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) p (Function.update (Memory.accessor memo1 p) m t) else p1 = p ∧ t1 = Memory.accessor memo1 p n ∧ Memory.colors memo2 = Function.update (Memory.colors memo1) p (Memory.color.Black (Option.some n)) ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) p (Function.update (Function.update (Memory.accessor memo1 p) n (Memory.accessor memo1 p m)) m t)) | _ => False)) → (if ¬s = (0 : ℤ) then let o2 : ℤ := s - (2 : ℤ); ((0 : ℤ) ≤ o2 + (1 : ℤ) → (GraphShape.well_colored_on graph g2 memo (Memory.colors memo2) ∧ p1 = t ∧ t1 = Memory.accessor memo p1 (0 : ℤ) ∧ Memory.colors memo2 p1 = Memory.color.Black (Option.some (0 : ℤ)) ∧ (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < s) ∧ ¬j = (0 : ℤ) → Memory.accessor memo2 p1 j = Memory.accessor memo1 p1 j) ∧ Memory.accessor memo2 p1 (0 : ℤ) = p ∧ (∀(l : Memory.loc) (n : ℤ), ¬l = Memory.null ∧ ¬l = p1 ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo2 l → Memory.accessor memo2 l n = Memory.accessor memo1 l n) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < (0 : ℤ) → (let l : Memory.loc := Memory.accessor memo2 p1 j; l = Memory.null ∨ GraphShape.black (Memory.colors memo2 l))) ∧ (∀(l : Memory.loc), ¬l = Memory.null → ¬GraphShape.path memo p1 l ∨ GraphShape.black (Memory.colors memo1 l) → Memory.colors memo2 l = Memory.colors memo1 l)) ∧ (∀(p2 : Memory.loc) (t2 : Memory.loc) (memo3 : Memory.memory), Memory.block_size memo3 = Memory.block_size memo2 → (∀(i : ℤ), ((0 : ℤ) ≤ i ∧ i ≤ o2) ∧ GraphShape.well_colored_on graph g2 memo (Memory.colors memo3) ∧ p2 = t ∧ t2 = Memory.accessor memo p2 i ∧ Memory.colors memo3 p2 = Memory.color.Black (Option.some i) ∧ (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < s) ∧ ¬j = i → Memory.accessor memo3 p2 j = Memory.accessor memo1 p2 j) ∧ Memory.accessor memo3 p2 i = p ∧ (∀(l : Memory.loc) (n : ℤ), ¬l = Memory.null ∧ ¬l = p2 ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo3 l → Memory.accessor memo3 l n = Memory.accessor memo1 l n) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < i → (let l : Memory.loc := Memory.accessor memo3 p2 j; l = Memory.null ∨ GraphShape.black (Memory.colors memo3 l))) ∧ (∀(l : Memory.loc), ¬l = Memory.null → ¬GraphShape.path memo p2 l ∨ GraphShape.black (Memory.colors memo1 l) → Memory.colors memo3 l = Memory.colors memo1 l) → (((0 : ℤ) ≤ Int.ofNat (Finset.card graph) - Int.ofNat (Finset.card gray) ∧ Int.ofNat (Finset.card graph) - Int.ofNat (Finset.card g2) < Int.ofNat (Finset.card graph) - Int.ofNat (Finset.card gray)) ∧ GraphShape.well_colored_on graph g2 memo (Memory.colors memo3) ∧ t2 ∈ graph ∧ (∀(x : Memory.loc) (n : ℤ), ¬x = Memory.null ∧ ¬GraphShape.black (Memory.colors memo3 x) ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo3 x → Memory.accessor memo3 x n = Memory.accessor memo x n)) ∧ (∀(memo4 : Memory.memory), Memory.block_size memo4 = Memory.block_size memo3 → GraphShape.unchanged memo3 memo4 ∧ GraphShape.well_colored_on graph g2 memo (Memory.colors memo4) ∧ (GraphShape.black (Memory.colors memo4 t2) ∨ t2 = Memory.null) ∧ (∀(x : Memory.loc), ¬x = Memory.null → ¬GraphShape.path memo t2 x ∨ GraphShape.black (Memory.colors memo3 x) → Memory.colors memo4 x = Memory.colors memo3 x) → (¬p2 = Memory.null ∧ (t2 = Memory.null ∨ GraphShape.black (Memory.colors memo4 t2)) → (match Memory.colors memo4 p2 with | Memory.color.Black (Option.some m) => (0 : ℤ) ≤ m ∧ m < Memory.block_size memo4 p2 | _ => False)) ∧ (∀(p3 : Memory.loc) (t3 : Memory.loc) (memo5 : Memory.memory), Memory.block_size memo5 = Memory.block_size memo4 → ((¬p2 = Memory.null ∨ ¬t2 = Memory.null ∧ ¬GraphShape.black (Memory.colors memo4 t2)) ∧ (¬t2 = Memory.null ∧ ¬GraphShape.black (Memory.colors memo4 t2) ∧ Memory.block_size memo4 t2 = (0 : ℤ) → Memory.colors memo5 = Function.update (Memory.colors memo4) t2 (Memory.color.Black Option.none) ∧ t3 = t2 ∧ p3 = p2 ∧ Memory.accessor memo5 = Memory.accessor memo4) ∧ (¬t2 = Memory.null ∧ ¬GraphShape.black (Memory.colors memo4 t2) ∧ (0 : ℤ) < Memory.block_size memo4 t2 → Memory.colors memo5 = Function.update (Memory.colors memo4) t2 (Memory.color.Black (Option.some (0 : ℤ))) ∧ t3 = Memory.accessor memo4 t2 (0 : ℤ) ∧ p3 = t2 ∧ Memory.accessor memo5 = Function.update (Memory.accessor memo4) t2 (Function.update (Memory.accessor memo4 t2) (0 : ℤ) p2)) ∧ (t2 = Memory.null ∨ GraphShape.black (Memory.colors memo4 t2) → (match Memory.colors memo4 p2 with | Memory.color.Black (Option.some m) => (let n : ℤ := m + (1 : ℤ); if n = Memory.block_size memo4 p2 then t3 = p2 ∧ p3 = Memory.accessor memo4 p2 m ∧ Memory.colors memo5 = Memory.colors memo4 ∧ Memory.accessor memo5 = Function.update (Memory.accessor memo4) p2 (Function.update (Memory.accessor memo4 p2) m t2) else p3 = p2 ∧ t3 = Memory.accessor memo4 p2 n ∧ Memory.colors memo5 = Function.update (Memory.colors memo4) p2 (Memory.color.Black (Option.some n)) ∧ Memory.accessor memo5 = Function.update (Memory.accessor memo4) p2 (Function.update (Function.update (Memory.accessor memo4 p2) n (Memory.accessor memo4 p2 m)) m t2)) | _ => False)) → GraphShape.well_colored_on graph g2 memo (Memory.colors memo5) ∧ p3 = t ∧ t3 = Memory.accessor memo p3 (i + (1 : ℤ)) ∧ Memory.colors memo5 p3 = Memory.color.Black (Option.some (i + (1 : ℤ))) ∧ (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < s) ∧ ¬j = i + (1 : ℤ) → Memory.accessor memo5 p3 j = Memory.accessor memo1 p3 j) ∧ Memory.accessor memo5 p3 (i + (1 : ℤ)) = p ∧ (∀(l : Memory.loc) (n : ℤ), ¬l = Memory.null ∧ ¬l = p3 ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo5 l → Memory.accessor memo5 l n = Memory.accessor memo1 l n) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < i + (1 : ℤ) → (let l : Memory.loc := Memory.accessor memo5 p3 j; l = Memory.null ∨ GraphShape.black (Memory.colors memo5 l))) ∧ (∀(l : Memory.loc), ¬l = Memory.null → ¬GraphShape.path memo p3 l ∨ GraphShape.black (Memory.colors memo1 l) → Memory.colors memo5 l = Memory.colors memo1 l)) ∧ ¬((p2 = Memory.null ∧ (t2 = Memory.null ∨ GraphShape.black (Memory.colors memo4 t2))) ∧ Memory.colors memo5 = Memory.colors memo4 ∧ Memory.accessor memo5 = Memory.accessor memo4)))) ∧ (GraphShape.well_colored_on graph g2 memo (Memory.colors memo3) ∧ p2 = t ∧ t2 = Memory.accessor memo p2 (o2 + (1 : ℤ)) ∧ Memory.colors memo3 p2 = Memory.color.Black (Option.some (o2 + (1 : ℤ))) ∧ (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j < s) ∧ ¬j = o2 + (1 : ℤ) → Memory.accessor memo3 p2 j = Memory.accessor memo1 p2 j) ∧ Memory.accessor memo3 p2 (o2 + (1 : ℤ)) = p ∧ (∀(l : Memory.loc) (n : ℤ), ¬l = Memory.null ∧ ¬l = p2 ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo3 l → Memory.accessor memo3 l n = Memory.accessor memo1 l n) ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < o2 + (1 : ℤ) → (let l : Memory.loc := Memory.accessor memo3 p2 j; l = Memory.null ∨ GraphShape.black (Memory.colors memo3 l))) ∧ (∀(l : Memory.loc), ¬l = Memory.null → ¬GraphShape.path memo p2 l ∨ GraphShape.black (Memory.colors memo1 l) → Memory.colors memo3 l = Memory.colors memo1 l) → (((0 : ℤ) ≤ Int.ofNat (Finset.card graph) - Int.ofNat (Finset.card gray) ∧ Int.ofNat (Finset.card graph) - Int.ofNat (Finset.card g2) < Int.ofNat (Finset.card graph) - Int.ofNat (Finset.card gray)) ∧ GraphShape.well_colored_on graph g2 memo (Memory.colors memo3) ∧ t2 ∈ graph ∧ (∀(x : Memory.loc) (n : ℤ), ¬x = Memory.null ∧ ¬GraphShape.black (Memory.colors memo3 x) ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo3 x → Memory.accessor memo3 x n = Memory.accessor memo x n)) ∧ (∀(memo4 : Memory.memory), Memory.block_size memo4 = Memory.block_size memo3 → GraphShape.unchanged memo3 memo4 ∧ GraphShape.well_colored_on graph g2 memo (Memory.colors memo4) ∧ (GraphShape.black (Memory.colors memo4 t2) ∨ t2 = Memory.null) ∧ (∀(x : Memory.loc), ¬x = Memory.null → ¬GraphShape.path memo t2 x ∨ GraphShape.black (Memory.colors memo3 x) → Memory.colors memo4 x = Memory.colors memo3 x) → (¬p2 = Memory.null ∧ (t2 = Memory.null ∨ GraphShape.black (Memory.colors memo4 t2)) → (match Memory.colors memo4 p2 with | Memory.color.Black (Option.some m) => (0 : ℤ) ≤ m ∧ m < Memory.block_size memo4 p2 | _ => False)) ∧ (∀(p3 : Memory.loc) (t3 : Memory.loc) (memo5 : Memory.memory), Memory.block_size memo5 = Memory.block_size memo4 → ((¬p2 = Memory.null ∨ ¬t2 = Memory.null ∧ ¬GraphShape.black (Memory.colors memo4 t2)) ∧ (¬t2 = Memory.null ∧ ¬GraphShape.black (Memory.colors memo4 t2) ∧ Memory.block_size memo4 t2 = (0 : ℤ) → Memory.colors memo5 = Function.update (Memory.colors memo4) t2 (Memory.color.Black Option.none) ∧ t3 = t2 ∧ p3 = p2 ∧ Memory.accessor memo5 = Memory.accessor memo4) ∧ (¬t2 = Memory.null ∧ ¬GraphShape.black (Memory.colors memo4 t2) ∧ (0 : ℤ) < Memory.block_size memo4 t2 → Memory.colors memo5 = Function.update (Memory.colors memo4) t2 (Memory.color.Black (Option.some (0 : ℤ))) ∧ t3 = Memory.accessor memo4 t2 (0 : ℤ) ∧ p3 = t2 ∧ Memory.accessor memo5 = Function.update (Memory.accessor memo4) t2 (Function.update (Memory.accessor memo4 t2) (0 : ℤ) p2)) ∧ (t2 = Memory.null ∨ GraphShape.black (Memory.colors memo4 t2) → (match Memory.colors memo4 p2 with | Memory.color.Black (Option.some m) => (let n : ℤ := m + (1 : ℤ); if n = Memory.block_size memo4 p2 then t3 = p2 ∧ p3 = Memory.accessor memo4 p2 m ∧ Memory.colors memo5 = Memory.colors memo4 ∧ Memory.accessor memo5 = Function.update (Memory.accessor memo4) p2 (Function.update (Memory.accessor memo4 p2) m t2) else p3 = p2 ∧ t3 = Memory.accessor memo4 p2 n ∧ Memory.colors memo5 = Function.update (Memory.colors memo4) p2 (Memory.color.Black (Option.some n)) ∧ Memory.accessor memo5 = Function.update (Memory.accessor memo4) p2 (Function.update (Function.update (Memory.accessor memo4 p2) n (Memory.accessor memo4 p2 m)) m t2)) | _ => False)) → (t3 = t ∧ p3 = p) ∧ GraphShape.unchanged memo1 memo5 ∧ GraphShape.well_colored_on graph gray memo (Memory.colors memo5) ∧ (GraphShape.black (Memory.colors memo5 t3) ∨ t3 = Memory.null) ∧ (∀(x : Memory.loc), ¬x = Memory.null → ¬GraphShape.path memo t3 x ∨ GraphShape.black (Memory.colors memo1 x) → Memory.colors memo5 x = Memory.colors memo1 x)) ∧ ¬((p2 = Memory.null ∧ (t2 = Memory.null ∨ GraphShape.black (Memory.colors memo4 t2))) ∧ Memory.colors memo5 = Memory.colors memo4 ∧ Memory.accessor memo5 = Memory.accessor memo4)))))) ∧ (o2 + (1 : ℤ) < (0 : ℤ) → (((0 : ℤ) ≤ Int.ofNat (Finset.card graph) - Int.ofNat (Finset.card gray) ∧ Int.ofNat (Finset.card graph) - Int.ofNat (Finset.card g2) < Int.ofNat (Finset.card graph) - Int.ofNat (Finset.card gray)) ∧ GraphShape.well_colored_on graph g2 memo (Memory.colors memo2) ∧ t1 ∈ graph ∧ (∀(x : Memory.loc) (n : ℤ), ¬x = Memory.null ∧ ¬GraphShape.black (Memory.colors memo2 x) ∧ (0 : ℤ) ≤ n ∧ n < Memory.block_size memo2 x → Memory.accessor memo2 x n = Memory.accessor memo x n)) ∧ (∀(memo3 : Memory.memory), Memory.block_size memo3 = Memory.block_size memo2 → GraphShape.unchanged memo2 memo3 ∧ GraphShape.well_colored_on graph g2 memo (Memory.colors memo3) ∧ (GraphShape.black (Memory.colors memo3 t1) ∨ t1 = Memory.null) ∧ (∀(x : Memory.loc), ¬x = Memory.null → ¬GraphShape.path memo t1 x ∨ GraphShape.black (Memory.colors memo2 x) → Memory.colors memo3 x = Memory.colors memo2 x) → (¬p1 = Memory.null ∧ (t1 = Memory.null ∨ GraphShape.black (Memory.colors memo3 t1)) → (match Memory.colors memo3 p1 with | Memory.color.Black (Option.some m) => (0 : ℤ) ≤ m ∧ m < Memory.block_size memo3 p1 | _ => False)) ∧ (∀(p2 : Memory.loc) (t2 : Memory.loc) (memo4 : Memory.memory), Memory.block_size memo4 = Memory.block_size memo3 → ((¬p1 = Memory.null ∨ ¬t1 = Memory.null ∧ ¬GraphShape.black (Memory.colors memo3 t1)) ∧ (¬t1 = Memory.null ∧ ¬GraphShape.black (Memory.colors memo3 t1) ∧ Memory.block_size memo3 t1 = (0 : ℤ) → Memory.colors memo4 = Function.update (Memory.colors memo3) t1 (Memory.color.Black Option.none) ∧ t2 = t1 ∧ p2 = p1 ∧ Memory.accessor memo4 = Memory.accessor memo3) ∧ (¬t1 = Memory.null ∧ ¬GraphShape.black (Memory.colors memo3 t1) ∧ (0 : ℤ) < Memory.block_size memo3 t1 → Memory.colors memo4 = Function.update (Memory.colors memo3) t1 (Memory.color.Black (Option.some (0 : ℤ))) ∧ t2 = Memory.accessor memo3 t1 (0 : ℤ) ∧ p2 = t1 ∧ Memory.accessor memo4 = Function.update (Memory.accessor memo3) t1 (Function.update (Memory.accessor memo3 t1) (0 : ℤ) p1)) ∧ (t1 = Memory.null ∨ GraphShape.black (Memory.colors memo3 t1) → (match Memory.colors memo3 p1 with | Memory.color.Black (Option.some m) => (let n : ℤ := m + (1 : ℤ); if n = Memory.block_size memo3 p1 then t2 = p1 ∧ p2 = Memory.accessor memo3 p1 m ∧ Memory.colors memo4 = Memory.colors memo3 ∧ Memory.accessor memo4 = Function.update (Memory.accessor memo3) p1 (Function.update (Memory.accessor memo3 p1) m t1) else p2 = p1 ∧ t2 = Memory.accessor memo3 p1 n ∧ Memory.colors memo4 = Function.update (Memory.colors memo3) p1 (Memory.color.Black (Option.some n)) ∧ Memory.accessor memo4 = Function.update (Memory.accessor memo3) p1 (Function.update (Function.update (Memory.accessor memo3 p1) n (Memory.accessor memo3 p1 m)) m t1)) | _ => False)) → (t2 = t ∧ p2 = p) ∧ GraphShape.unchanged memo1 memo4 ∧ GraphShape.well_colored_on graph gray memo (Memory.colors memo4) ∧ (GraphShape.black (Memory.colors memo4 t2) ∨ t2 = Memory.null) ∧ (∀(x : Memory.loc), ¬x = Memory.null → ¬GraphShape.path memo t2 x ∨ GraphShape.black (Memory.colors memo1 x) → Memory.colors memo4 x = Memory.colors memo1 x)) ∧ ¬((p1 = Memory.null ∧ (t1 = Memory.null ∨ GraphShape.black (Memory.colors memo3 t1))) ∧ Memory.colors memo4 = Memory.colors memo3 ∧ Memory.accessor memo4 = Memory.accessor memo3)))) else (t1 = t ∧ p1 = p) ∧ GraphShape.unchanged memo1 memo2 ∧ GraphShape.well_colored_on graph gray memo (Memory.colors memo2) ∧ (GraphShape.black (Memory.colors memo2 t1) ∨ t1 = Memory.null) ∧ (∀(x : Memory.loc), ¬x = Memory.null → ¬GraphShape.path memo t1 x ∨ GraphShape.black (Memory.colors memo1 x) → Memory.colors memo2 x = Memory.colors memo1 x))) ∧ ¬((p = Memory.null ∧ (t = Memory.null ∨ GraphShape.black (Memory.colors memo1 t))) ∧ Memory.colors memo2 = Memory.colors memo1 ∧ Memory.accessor memo2 = Memory.accessor memo1)))))))) ∧ (let o1 : Finset Memory.loc := (∅ : Finset Memory.loc); (GraphShape.well_colored_on graph o1 memo (Memory.colors memo) ∧ root ∈ graph) ∧ (∀(memo1 : Memory.memory), Memory.block_size memo1 = Memory.block_size memo → GraphShape.unchanged memo memo1 ∧ GraphShape.well_colored_on graph o1 memo (Memory.colors memo1) ∧ (GraphShape.black (Memory.colors memo1 root) ∨ root = Memory.null) ∧ (∀(x : Memory.loc), ¬x = Memory.null → ¬GraphShape.path memo root x ∨ GraphShape.black (Memory.colors memo x) → Memory.colors memo1 x = Memory.colors memo x) → (¬True ∧ (root = Memory.null ∨ GraphShape.black (Memory.colors memo1 root)) → (match Memory.colors memo1 Memory.null with | Memory.color.Black (Option.some m) => (0 : ℤ) ≤ m ∧ m < Memory.block_size memo1 Memory.null | _ => False)) ∧ (∀(p : Memory.loc) (t : Memory.loc) (memo2 : Memory.memory), Memory.block_size memo2 = Memory.block_size memo1 → ¬((¬True ∨ ¬root = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 root)) ∧ (¬root = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 root) ∧ Memory.block_size memo1 root = (0 : ℤ) → Memory.colors memo2 = Function.update (Memory.colors memo1) root (Memory.color.Black Option.none) ∧ t = root ∧ p = Memory.null ∧ Memory.accessor memo2 = Memory.accessor memo1) ∧ (¬root = Memory.null ∧ ¬GraphShape.black (Memory.colors memo1 root) ∧ (0 : ℤ) < Memory.block_size memo1 root → Memory.colors memo2 = Function.update (Memory.colors memo1) root (Memory.color.Black (Option.some (0 : ℤ))) ∧ t = Memory.accessor memo1 root (0 : ℤ) ∧ p = root ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) root (Function.update (Memory.accessor memo1 root) (0 : ℤ) Memory.null)) ∧ (root = Memory.null ∨ GraphShape.black (Memory.colors memo1 root) → (match Memory.colors memo1 Memory.null with | Memory.color.Black (Option.some m) => (let n : ℤ := m + (1 : ℤ); if n = Memory.block_size memo1 Memory.null then t = Memory.null ∧ p = Memory.accessor memo1 Memory.null m ∧ Memory.colors memo2 = Memory.colors memo1 ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) Memory.null (Function.update (Memory.accessor memo1 Memory.null) m root) else p = Memory.null ∧ t = Memory.accessor memo1 Memory.null n ∧ Memory.colors memo2 = Function.update (Memory.colors memo1) Memory.null (Memory.color.Black (Option.some n)) ∧ Memory.accessor memo2 = Function.update (Memory.accessor memo1) Memory.null (Function.update (Function.update (Memory.accessor memo1 Memory.null) n (Memory.accessor memo1 Memory.null m)) m root)) | _ => False))) ∧ ((root = Memory.null ∨ GraphShape.black (Memory.colors memo1 root)) ∧ Memory.colors memo2 = Memory.colors memo1 ∧ Memory.accessor memo2 = Memory.accessor memo1 → GraphShape.unchanged memo memo2 ∧ (∀(x : Memory.loc), GraphShape.path memo root x ∧ ¬x = Memory.null → GraphShape.black (Memory.colors memo2 x)) ∧ (∀(x : Memory.loc), ¬GraphShape.path memo root x ∧ ¬x = Memory.null → Memory.colors memo2 x = Memory.colors memo x)))))
  := sorry
end schorr_waite_via_recursion_SchorrWaite_schorr_waiteqtvc
