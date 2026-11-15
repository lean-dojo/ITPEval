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
namespace KodaRuskey_Spec
inductive color where
  | White : color
  | Black : color
axiom inhabited_axiom_color : Inhabited color
attribute [instance] inhabited_axiom_color
inductive forest where
  | E : forest
  | N : ℤ -> forest -> forest -> forest
axiom inhabited_axiom_forest : Inhabited forest
attribute [instance] inhabited_axiom_forest
axiom coloring : Type
axiom inhabited_axiom_coloring : Inhabited coloring
attribute [instance] inhabited_axiom_coloring
noncomputable def size_forest : forest -> ℤ
  | forest.E => (0 : ℤ)
  | (forest.N x f1 f2) => (1 : ℤ) + size_forest f1 + size_forest f2
noncomputable def mem_forest : ℤ -> forest -> Prop
  | n, forest.E => False
  | n, (forest.N i f1 f2) => i = n ∨ mem_forest n f1 ∨ mem_forest n f2
noncomputable def between_range_forest (i : ℤ) (j : ℤ) (f : forest) := ∀(n : ℤ), mem_forest n f → i ≤ n ∧ n < j
noncomputable def disjoint (f1 : forest) (f2 : forest) := ∀(x : ℤ), mem_forest x f1 → ¬mem_forest x f2
noncomputable def no_repeated_forest : forest -> Prop
  | forest.E => True
  | (forest.N i f1 f2) => no_repeated_forest f1 ∧ no_repeated_forest f2 ∧ ¬mem_forest i f1 ∧ ¬mem_forest i f2 ∧ disjoint f1 f2
noncomputable def valid_nums_forest (f : forest) (n : ℤ) := between_range_forest (0 : ℤ) n f ∧ no_repeated_forest f
noncomputable def white_forest : forest -> (ℤ -> color) -> Prop
  | forest.E, c => True
  | (forest.N i f1 f2), c => c i = color.White ∧ white_forest f1 c ∧ white_forest f2 c
noncomputable def valid_coloring : forest -> (ℤ -> color) -> Prop
  | forest.E, c => True
  | (forest.N i f1 f2), c => valid_coloring f2 c ∧ (match c i with | color.White => white_forest f1 c | color.Black => valid_coloring f1 c)
noncomputable def count_forest : forest -> ℤ
  | forest.E => (1 : ℤ)
  | (forest.N x f1 f2) => ((1 : ℤ) + count_forest f1) * count_forest f2
noncomputable def eq_coloring (n : ℤ) (c1 : ℤ -> color) (c2 : ℤ -> color) := ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → c1 i = c2 i
end KodaRuskey_Spec
namespace Lemmas
axiom stack : Type
axiom inhabited_axiom_stack : Inhabited stack
attribute [instance] inhabited_axiom_stack
noncomputable def mem_stack : ℤ -> List KodaRuskey_Spec.forest -> Prop
  | n, ([] : List KodaRuskey_Spec.forest) => False
  | n, (List.cons f tl) => KodaRuskey_Spec.mem_forest n f ∨ mem_stack n tl
noncomputable def size_stack : List KodaRuskey_Spec.forest -> ℤ
  | ([] : List KodaRuskey_Spec.forest) => (0 : ℤ)
  | (List.cons f st1) => KodaRuskey_Spec.size_forest f + size_stack st1
noncomputable def even_forest : KodaRuskey_Spec.forest -> Prop
  | KodaRuskey_Spec.forest.E => False
  | (KodaRuskey_Spec.forest.N x f1 f2) => ¬even_forest f1 ∨ even_forest f2
noncomputable def final_forest : KodaRuskey_Spec.forest -> (ℤ -> KodaRuskey_Spec.color) -> Prop
  | KodaRuskey_Spec.forest.E, c => True
  | (KodaRuskey_Spec.forest.N i f1 f2), c => c i = KodaRuskey_Spec.color.Black ∧ final_forest f1 c ∧ (if ¬even_forest f1 then KodaRuskey_Spec.white_forest f2 c else final_forest f2 c)
noncomputable def any_forest (f : KodaRuskey_Spec.forest) (c : ℤ -> KodaRuskey_Spec.color) := KodaRuskey_Spec.white_forest f c ∨ final_forest f c
noncomputable def unchanged (st : List KodaRuskey_Spec.forest) (c1 : ℤ -> KodaRuskey_Spec.color) (c2 : ℤ -> KodaRuskey_Spec.color) := ∀(i : ℤ), mem_stack i st → c1 i = c2 i
noncomputable def inverse : List KodaRuskey_Spec.forest -> (ℤ -> KodaRuskey_Spec.color) -> (ℤ -> KodaRuskey_Spec.color) -> Prop
  | ([] : List KodaRuskey_Spec.forest), c1, c2 => True
  | (List.cons f st'), c1, c2 => (KodaRuskey_Spec.white_forest f c1 ∧ final_forest f c2 ∨ final_forest f c1 ∧ KodaRuskey_Spec.white_forest f c2) ∧ (if even_forest f then unchanged st' c1 c2 else inverse st' c1 c2)
noncomputable def any_stack : List KodaRuskey_Spec.forest -> (ℤ -> KodaRuskey_Spec.color) -> Prop
  | ([] : List KodaRuskey_Spec.forest), c => True
  | (List.cons f st1), c => (KodaRuskey_Spec.white_forest f c ∨ final_forest f c) ∧ any_stack st1 c
inductive sub : List KodaRuskey_Spec.forest -> KodaRuskey_Spec.forest -> (ℤ -> KodaRuskey_Spec.color) -> Prop where
 | Sub_reflex (f : KodaRuskey_Spec.forest) (c : ℤ -> KodaRuskey_Spec.color) : sub (List.cons f ([] : List KodaRuskey_Spec.forest)) f c
 | Sub_brother (st : List KodaRuskey_Spec.forest) (f2 : KodaRuskey_Spec.forest) (c : ℤ -> KodaRuskey_Spec.color) (i : ℤ) (f1 : KodaRuskey_Spec.forest) : sub st f2 c → sub st (KodaRuskey_Spec.forest.N i f1 f2) c
 | Sub_append (st : List KodaRuskey_Spec.forest) (f1 : KodaRuskey_Spec.forest) (c : ℤ -> KodaRuskey_Spec.color) (i : ℤ) (f2 : KodaRuskey_Spec.forest) : sub st f1 c → c i = KodaRuskey_Spec.color.Black → sub (st ++ List.cons f2 ([] : List KodaRuskey_Spec.forest)) (KodaRuskey_Spec.forest.N i f1 f2) c
noncomputable def disjoint_stack (f : KodaRuskey_Spec.forest) (st : List KodaRuskey_Spec.forest) := ∀(i : ℤ), KodaRuskey_Spec.mem_forest i f → ¬mem_stack i st
noncomputable def count_stack : List KodaRuskey_Spec.forest -> ℤ
  | ([] : List KodaRuskey_Spec.forest) => (1 : ℤ)
  | (List.cons f st') => KodaRuskey_Spec.count_forest f * count_stack st'
axiom visited : Type
axiom inhabited_axiom_visited : Inhabited visited
attribute [instance] inhabited_axiom_visited
noncomputable def stored_solutions (f0 : KodaRuskey_Spec.forest) (bits : ℤ -> KodaRuskey_Spec.color) (st : List KodaRuskey_Spec.forest) (v1 : List (ℤ -> KodaRuskey_Spec.color)) (v2 : List (ℤ -> KodaRuskey_Spec.color)) := let n : ℤ := KodaRuskey_Spec.size_forest f0; let start : ℤ := Int.ofNat (List.length v1); let stop : ℤ := Int.ofNat (List.length v2); stop - start = count_stack st ∧ (∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < start → KodaRuskey_Spec.eq_coloring n (v2[Int.toNat j]!) (v1[Int.toNat j]!)) ∧ (∀(j : ℤ), start ≤ j ∧ j < stop → KodaRuskey_Spec.valid_coloring f0 (v2[Int.toNat j]!) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → ¬mem_stack i st → v2[Int.toNat j]! i = bits i) ∧ (∀(k : ℤ), start ≤ k ∧ k < stop → ¬j = k → ¬KodaRuskey_Spec.eq_coloring n (v2[Int.toNat j]!) (v2[Int.toNat k]!)))
end Lemmas
namespace koda_ruskey_KodaRuskey_mainqtvc
theorem main'vc (f0 : KodaRuskey_Spec.forest) (bits : List KodaRuskey_Spec.color) (fact0 : KodaRuskey_Spec.white_forest f0 (getElem! bits ∘ Int.toNat)) (fact1 : KodaRuskey_Spec.size_forest f0 = Int.ofNat (List.length bits)) (fact2 : KodaRuskey_Spec.valid_nums_forest f0 (Int.ofNat (List.length bits))) : let o1 : List KodaRuskey_Spec.forest := List.cons f0 ([] : List KodaRuskey_Spec.forest); (KodaRuskey_Spec.size_forest f0 = Int.ofNat (List.length bits) ∧ KodaRuskey_Spec.valid_nums_forest f0 (Int.ofNat (List.length bits)) ∧ Lemmas.sub o1 f0 (getElem! bits ∘ Int.toNat) ∧ Lemmas.any_stack o1 (getElem! bits ∘ Int.toNat) ∧ KodaRuskey_Spec.valid_coloring f0 (getElem! bits ∘ Int.toNat)) ∧ (∀(bits1 : List KodaRuskey_Spec.color) (visited : List (ℤ -> KodaRuskey_Spec.color)), List.length bits1 = List.length bits → (∀(i : ℤ), ¬Lemmas.mem_stack i o1 → bits1[Int.toNat i]! = bits[Int.toNat i]!) ∧ Lemmas.inverse o1 (getElem! bits ∘ Int.toNat) (getElem! bits1 ∘ Int.toNat) ∧ KodaRuskey_Spec.valid_coloring f0 (getElem! bits1 ∘ Int.toNat) ∧ Lemmas.stored_solutions f0 (getElem! bits1 ∘ Int.toNat) o1 ([] : List (ℤ -> KodaRuskey_Spec.color)) visited → Int.ofNat (List.length visited) = KodaRuskey_Spec.count_forest f0 ∧ (let n : ℤ := Int.ofNat (List.length visited); ∀(j : ℤ), (0 : ℤ) ≤ j ∧ j < n → KodaRuskey_Spec.valid_coloring f0 (visited[Int.toNat j]!) ∧ (∀(k : ℤ), (0 : ℤ) ≤ k ∧ k < n → ¬j = k → ¬KodaRuskey_Spec.eq_coloring (Int.ofNat (List.length bits1)) (visited[Int.toNat j]!) (visited[Int.toNat k]!))))
  := sorry
end koda_ruskey_KodaRuskey_mainqtvc
