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

namespace verifythis_2018_le_rouge_et_le_noir_1_ColoredTiles_enumqtvc
inductive color where
  | Red : color
  | Black : color
axiom inhabited_axiom_color : Inhabited color
attribute [instance] inhabited_axiom_color
axiom coloring : Type
axiom inhabited_axiom_coloring : Inhabited coloring
attribute [instance] inhabited_axiom_coloring
noncomputable def tworedneighbors (c : List color) (i : ℤ) := getElem! c (Int.toNat (i - (2 : ℤ))) = color.Red ∧ getElem! c (Int.toNat (i - (1 : ℤ))) = color.Red ∧ (2 : ℤ) ≤ i ∨ getElem! c (Int.toNat (i - (1 : ℤ))) = color.Red ∧ getElem! c (Int.toNat (i + (1 : ℤ))) = color.Red ∧ (1 : ℤ) ≤ i ∧ i ≤ Int.ofNat (List.length c) - (2 : ℤ) ∨ getElem! c (Int.toNat (i + (1 : ℤ))) = color.Red ∧ getElem! c (Int.toNat (i + (2 : ℤ))) = color.Red ∧ i ≤ Int.ofNat (List.length c) - (3 : ℤ)
noncomputable def valid (c : List color) := ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length c) → getElem! c (Int.toNat i) = color.Red → tworedneighbors c i
axiom first_black_tile : List color -> ℤ
axiom first_black_tile'def (c : List color) : if Int.ofNat (List.length c) = (0 : ℤ) then first_black_tile c = (0 : ℤ) else match getElem! c (0 : ℕ) with | color.Black => first_black_tile c = (0 : ℤ) | color.Red => first_black_tile c = (1 : ℤ) + first_black_tile (List.drop (1 : ℕ) c)
axiom first_black_tile'spec'2 (c : List color) : (0 : ℤ) ≤ first_black_tile c ∧ first_black_tile c ≤ Int.ofNat (List.length c)
axiom first_black_tile'spec'1 (j : ℤ) (c : List color) (fact0 : (0 : ℤ) ≤ j) (fact1 : j < first_black_tile c) (fact2 : first_black_tile c ≤ Int.ofNat (List.length c)) : getElem! c (Int.toNat j) = color.Red
axiom first_black_tile'spec'0 (c : List color) (fact0 : first_black_tile c < Int.ofNat (List.length c)) : getElem! c (Int.toNat (first_black_tile c)) = color.Black
axiom first_black_tile'spec (c : List color) (fact0 : valid c) : first_black_tile c = (0 : ℤ) ∨ (3 : ℤ) ≤ first_black_tile c
axiom addleft : ℤ -> List color -> List color
axiom addleft'def (nr : ℤ) (c : List color) : if nr ≤ (0 : ℤ) then addleft nr c = List.cons color.Black c else addleft nr c = List.cons color.Red (addleft (nr - (1 : ℤ)) c)
axiom addleft'spec (nr : ℤ) (c : List color) (fact0 : (0 : ℤ) ≤ nr) : Int.ofNat (List.length (addleft nr c)) = Int.ofNat (List.length c) + nr + (1 : ℤ)
axiom addleft_closure : ℤ -> List color -> List color
axiom addleft_closure_def (y : ℤ) (y1 : List color) : addleft_closure y y1 = addleft y y1
noncomputable def mapaddleft (s : Finset (List color)) (nr : ℤ) := Finset.image (addleft_closure nr) s
noncomputable def reciprocal {β : Type} {α : Type} [Inhabited β] [Inhabited α] (f : α -> β) (g : β -> α) := ∀(y : α), g (f y) = y
noncomputable def rmleft (nr : ℤ) (c : List color) := List.drop (Int.toNat (nr + (1 : ℤ))) c
axiom fc : ℤ -> color
axiom fc1 : ℤ -> color
axiom fc2 : ℤ -> color
axiom fc3 : ℤ -> color
axiom fc4 : ℤ -> color
axiom fc5 : ℤ -> color
axiom fc6 : ℤ -> color
axiom fc'def (y0 : ℤ) : fc y0 = color.Black
axiom fc'def1 (y0 : ℤ) : fc1 y0 = color.Black
axiom fc'def2 (y0 : ℤ) : fc2 y0 = color.Black
axiom fc'def3 (y0 : ℤ) : fc3 y0 = color.Red
axiom fc'def4 (y0 : ℤ) : fc4 y0 = color.Black
axiom fc'def5 (y0 : ℤ) : fc5 y0 = color.Red
axiom fc'def6 (y0 : ℤ) : fc6 y0 = color.Red
theorem enum'vc : (0 : ℤ) ≤ (51 : ℤ) ∧ (∀(count : List ℤ), (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (51 : ℤ) → count[Int.toNat i]! = (0 : ℤ)) ∧ Int.ofNat (List.length count) = (51 : ℤ) → (0 : ℤ) ≤ (51 : ℤ) ∧ (∀(sets : List (Finset (List color))), (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (51 : ℤ) → sets[Int.toNat i]! = (∅ : Finset (List color))) ∧ Int.ofNat (List.length sets) = (51 : ℤ) → ((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) < Int.ofNat (List.length count)) ∧ (List.length (List.set count (0 : ℕ) (1 : ℤ)) = List.length count → getElem! (List.set count (0 : ℕ) (1 : ℤ)) ∘ Int.toNat = Function.update (getElem! count ∘ Int.toNat) (0 : ℤ) (1 : ℤ) → (let o1 : Finset (List color) := insert (List.create (0 : ℕ) (fc ∘ Int.ofNat)) (∅ : Finset (List color)); ((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) < Int.ofNat (List.length sets)) ∧ (List.length (List.set sets (0 : ℕ) o1) = List.length sets → getElem! (List.set sets (0 : ℕ) o1) ∘ Int.toNat = Function.update (getElem! sets ∘ Int.toNat) (0 : ℤ) o1 → ((0 : ℤ) ≤ (1 : ℤ) ∧ (1 : ℤ) < Int.ofNat (List.length (List.set count (0 : ℕ) (1 : ℤ)))) ∧ (List.length (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) = List.length (List.set count (0 : ℕ) (1 : ℤ)) → getElem! (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) ∘ Int.toNat = Function.update (getElem! (List.set count (0 : ℕ) (1 : ℤ)) ∘ Int.toNat) (1 : ℤ) (1 : ℤ) → (let o2 : Finset (List color) := insert (List.create (1 : ℕ) (fc1 ∘ Int.ofNat)) (∅ : Finset (List color)); ((0 : ℤ) ≤ (1 : ℤ) ∧ (1 : ℤ) < Int.ofNat (List.length (List.set sets (0 : ℕ) o1))) ∧ (List.length (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) = List.length (List.set sets (0 : ℕ) o1) → getElem! (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) ∘ Int.toNat = Function.update (getElem! (List.set sets (0 : ℕ) o1) ∘ Int.toNat) (1 : ℤ) o2 → ((0 : ℤ) ≤ (2 : ℤ) ∧ (2 : ℤ) < Int.ofNat (List.length (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)))) ∧ (List.length (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)) = List.length (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) → getElem! (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)) ∘ Int.toNat = Function.update (getElem! (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) ∘ Int.toNat) (2 : ℤ) (1 : ℤ) → (let o3 : Finset (List color) := insert (List.create (2 : ℕ) (fc2 ∘ Int.ofNat)) (∅ : Finset (List color)); ((0 : ℤ) ≤ (2 : ℤ) ∧ (2 : ℤ) < Int.ofNat (List.length (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2))) ∧ (List.length (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) = List.length (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) → getElem! (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) ∘ Int.toNat = Function.update (getElem! (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) ∘ Int.toNat) (2 : ℤ) o3 → ((0 : ℤ) ≤ (3 : ℤ) ∧ (3 : ℤ) < Int.ofNat (List.length (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)))) ∧ (List.length (List.set (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)) (3 : ℕ) (2 : ℤ)) = List.length (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)) → getElem! (List.set (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)) (3 : ℕ) (2 : ℤ)) ∘ Int.toNat = Function.update (getElem! (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)) ∘ Int.toNat) (3 : ℤ) (2 : ℤ) → (let o4 : Finset (List color) := insert (List.create (3 : ℕ) (fc3 ∘ Int.ofNat)) (insert (List.create (3 : ℕ) (fc4 ∘ Int.ofNat)) (∅ : Finset (List color))); ((0 : ℤ) ≤ (3 : ℤ) ∧ (3 : ℤ) < Int.ofNat (List.length (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3))) ∧ (List.length (List.set (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) (3 : ℕ) o4) = List.length (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) → getElem! (List.set (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) (3 : ℕ) o4) ∘ Int.toNat = Function.update (getElem! (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) ∘ Int.toNat) (3 : ℤ) o4 → ((4 : ℤ) ≤ (50 : ℤ) + (1 : ℤ) → ((∀(c : List color), (0 : ℤ) ≤ Int.ofNat (List.length c) ∧ Int.ofNat (List.length c) < (4 : ℤ) → valid c → c ∈ (List.set (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) (3 : ℕ) o4)[List.length c]!) ∧ (∀(c : List color) (i : ℤ), (0 : ℤ) ≤ i ∧ i < (4 : ℤ) → c ∈ (List.set (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) (3 : ℕ) o4)[Int.toNat i]! → Int.ofNat (List.length c) = i ∧ valid c) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (4 : ℤ) → (List.set (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)) (3 : ℕ) (2 : ℤ))[Int.toNat i]! = Int.ofNat (Finset.card ((List.set (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) (3 : ℕ) o4)[Int.toNat i]!)))) ∧ (∀(sets1 : List (Finset (List color))) (count1 : List ℤ), List.length sets1 = List.length (List.set (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) (3 : ℕ) o4) → List.length count1 = List.length (List.set (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)) (3 : ℕ) (2 : ℤ)) → (∀(n : ℤ), ((4 : ℤ) ≤ n ∧ n ≤ (50 : ℤ)) ∧ (∀(c : List color), (0 : ℤ) ≤ Int.ofNat (List.length c) ∧ Int.ofNat (List.length c) < n → valid c → c ∈ sets1[List.length c]!) ∧ (∀(c : List color) (i : ℤ), (0 : ℤ) ≤ i ∧ i < n → c ∈ sets1[Int.toNat i]! → Int.ofNat (List.length c) = i ∧ valid c) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → count1[Int.toNat i]! = Int.ofNat (Finset.card (sets1[Int.toNat i]!))) → (let o5 : ℤ := n - (1 : ℤ); ((0 : ℤ) ≤ o5 ∧ o5 < Int.ofNat (List.length count1)) ∧ (let o6 : ℤ := count1[Int.toNat o5]!; ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length count1)) ∧ (List.length (List.set count1 (Int.toNat n) o6) = List.length count1 → getElem! (List.set count1 (Int.toNat n) o6) ∘ Int.toNat = Function.update (getElem! count1 ∘ Int.toNat) n o6 → (let o7 : ℤ := n - (1 : ℤ); ((0 : ℤ) ≤ o7 ∧ o7 < Int.ofNat (List.length sets1)) ∧ (let o8 : Finset (List color) := mapaddleft (sets1[Int.toNat o7]!) (0 : ℤ); ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length sets1)) ∧ (List.length (List.set sets1 (Int.toNat n) o8) = List.length sets1 → getElem! (List.set sets1 (Int.toNat n) o8) ∘ Int.toNat = Function.update (getElem! sets1 ∘ Int.toNat) n o8 → (let o9 : ℤ := n - (1 : ℤ); ((3 : ℤ) ≤ o9 + (1 : ℤ) → ((∀(c : List color), (0 : ℤ) ≤ Int.ofNat (List.length c) ∧ Int.ofNat (List.length c) < n → valid c → c ∈ (List.set sets1 (Int.toNat n) o8)[List.length c]!) ∧ (∀(c : List color) (i : ℤ), (0 : ℤ) ≤ i ∧ i < n → c ∈ (List.set sets1 (Int.toNat n) o8)[Int.toNat i]! → Int.ofNat (List.length c) = i ∧ valid c) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → (List.set count1 (Int.toNat n) o6)[Int.toNat i]! = Int.ofNat (Finset.card ((List.set sets1 (Int.toNat n) o8)[Int.toNat i]!))) ∧ (∀(c : List color), (c ∈ (List.set sets1 (Int.toNat n) o8)[Int.toNat n]!) = (Int.ofNat (List.length c) = n ∧ valid c ∧ first_black_tile c < (3 : ℤ))) ∧ (List.set count1 (Int.toNat n) o6)[Int.toNat n]! = Int.ofNat (Finset.card ((List.set sets1 (Int.toNat n) o8)[Int.toNat n]!))) ∧ (∀(sets2 : List (Finset (List color))) (count2 : List ℤ), List.length sets2 = List.length (List.set sets1 (Int.toNat n) o8) → List.length count2 = List.length (List.set count1 (Int.toNat n) o6) → (∀(k : ℤ), ((3 : ℤ) ≤ k ∧ k ≤ o9) ∧ (∀(c : List color), (0 : ℤ) ≤ Int.ofNat (List.length c) ∧ Int.ofNat (List.length c) < n → valid c → c ∈ sets2[List.length c]!) ∧ (∀(c : List color) (i : ℤ), (0 : ℤ) ≤ i ∧ i < n → c ∈ sets2[Int.toNat i]! → Int.ofNat (List.length c) = i ∧ valid c) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → count2[Int.toNat i]! = Int.ofNat (Finset.card (sets2[Int.toNat i]!))) ∧ (∀(c : List color), (c ∈ sets2[Int.toNat n]!) = (Int.ofNat (List.length c) = n ∧ valid c ∧ first_black_tile c < k)) ∧ count2[Int.toNat n]! = Int.ofNat (Finset.card (sets2[Int.toNat n]!)) → (let o10 : ℤ := n - k - (1 : ℤ); ((0 : ℤ) ≤ o10 ∧ o10 < Int.ofNat (List.length count2)) ∧ ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length count2)) ∧ (let o11 : ℤ := count2[Int.toNat n]! + count2[Int.toNat o10]!; ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length count2)) ∧ (List.length (List.set count2 (Int.toNat n) o11) = List.length count2 → getElem! (List.set count2 (Int.toNat n) o11) ∘ Int.toNat = Function.update (getElem! count2 ∘ Int.toNat) n o11 → (let o12 : ℤ := n - k - (1 : ℤ); ((0 : ℤ) ≤ o12 ∧ o12 < Int.ofNat (List.length sets2)) ∧ (let ns : Finset (List color) := mapaddleft (sets2[Int.toNat o12]!) k; ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length sets2)) ∧ (let o13 : Finset (List color) := sets2[Int.toNat n]!; (∀(x : List color), x ∈ o13 → ¬x ∈ ns) ∧ (let o14 : Finset (List color) := o13 ∪ ns; Int.ofNat (Finset.card o14) = Int.ofNat (Finset.card o13) + Int.ofNat (Finset.card ns) → ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length sets2)) ∧ (List.length (List.set sets2 (Int.toNat n) o14) = List.length sets2 → getElem! (List.set sets2 (Int.toNat n) o14) ∘ Int.toNat = Function.update (getElem! sets2 ∘ Int.toNat) n o14 → (∀(c : List color), (0 : ℤ) ≤ Int.ofNat (List.length c) ∧ Int.ofNat (List.length c) < n → valid c → c ∈ (List.set sets2 (Int.toNat n) o14)[List.length c]!) ∧ (∀(c : List color) (i : ℤ), (0 : ℤ) ≤ i ∧ i < n → c ∈ (List.set sets2 (Int.toNat n) o14)[Int.toNat i]! → Int.ofNat (List.length c) = i ∧ valid c) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → (List.set count2 (Int.toNat n) o11)[Int.toNat i]! = Int.ofNat (Finset.card ((List.set sets2 (Int.toNat n) o14)[Int.toNat i]!))) ∧ (∀(c : List color), (c ∈ (List.set sets2 (Int.toNat n) o14)[Int.toNat n]!) = (Int.ofNat (List.length c) = n ∧ valid c ∧ first_black_tile c < k + (1 : ℤ))) ∧ (List.set count2 (Int.toNat n) o11)[Int.toNat n]! = Int.ofNat (Finset.card ((List.set sets2 (Int.toNat n) o14)[Int.toNat n]!))))))))))) ∧ ((∀(c : List color), (0 : ℤ) ≤ Int.ofNat (List.length c) ∧ Int.ofNat (List.length c) < n → valid c → c ∈ sets2[List.length c]!) ∧ (∀(c : List color) (i : ℤ), (0 : ℤ) ≤ i ∧ i < n → c ∈ sets2[Int.toNat i]! → Int.ofNat (List.length c) = i ∧ valid c) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → count2[Int.toNat i]! = Int.ofNat (Finset.card (sets2[Int.toNat i]!))) ∧ (∀(c : List color), (c ∈ sets2[Int.toNat n]!) = (Int.ofNat (List.length c) = n ∧ valid c ∧ first_black_tile c < o9 + (1 : ℤ))) ∧ count2[Int.toNat n]! = Int.ofNat (Finset.card (sets2[Int.toNat n]!)) → (let o10 : ℤ -> color := fc5; (0 : ℤ) ≤ n ∧ (let r : List color := List.create (Int.toNat n) (o10 ∘ Int.ofNat); Int.ofNat (List.length r) = n ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → r[Int.toNat i]! = o10 i) → (let sr : Finset (List color) := insert r (∅ : Finset (List color)); ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length count2)) ∧ (let o11 : ℤ := count2[Int.toNat n]! + (1 : ℤ); ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length count2)) ∧ (List.length (List.set count2 (Int.toNat n) o11) = List.length count2 → getElem! (List.set count2 (Int.toNat n) o11) ∘ Int.toNat = Function.update (getElem! count2 ∘ Int.toNat) n o11 → ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length sets2)) ∧ (let o12 : Finset (List color) := sets2[Int.toNat n]!; (∀(x : List color), x ∈ o12 → ¬x ∈ sr) ∧ (let o13 : Finset (List color) := o12 ∪ sr; Int.ofNat (Finset.card o13) = Int.ofNat (Finset.card o12) + Int.ofNat (Finset.card sr) → ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length sets2)) ∧ (List.length (List.set sets2 (Int.toNat n) o13) = List.length sets2 → getElem! (List.set sets2 (Int.toNat n) o13) ∘ Int.toNat = Function.update (getElem! sets2 ∘ Int.toNat) n o13 → (∀(c : List color), (0 : ℤ) ≤ Int.ofNat (List.length c) ∧ Int.ofNat (List.length c) < n + (1 : ℤ) → valid c → c ∈ (List.set sets2 (Int.toNat n) o13)[List.length c]!) ∧ (∀(c : List color) (i : ℤ), (0 : ℤ) ≤ i ∧ i < n + (1 : ℤ) → c ∈ (List.set sets2 (Int.toNat n) o13)[Int.toNat i]! → Int.ofNat (List.length c) = i ∧ valid c) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n + (1 : ℤ) → (List.set count2 (Int.toNat n) o11)[Int.toNat i]! = Int.ofNat (Finset.card ((List.set sets2 (Int.toNat n) o13)[Int.toNat i]!)))))))))))))) ∧ (o9 + (1 : ℤ) < (3 : ℤ) → (let o10 : ℤ -> color := fc6; (0 : ℤ) ≤ n ∧ (let r : List color := List.create (Int.toNat n) (o10 ∘ Int.ofNat); Int.ofNat (List.length r) = n ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → r[Int.toNat i]! = o10 i) → (let sr : Finset (List color) := insert r (∅ : Finset (List color)); ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length (List.set count1 (Int.toNat n) o6))) ∧ (let o11 : ℤ := (List.set count1 (Int.toNat n) o6)[Int.toNat n]! + (1 : ℤ); ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length (List.set count1 (Int.toNat n) o6))) ∧ (List.length (List.set (List.set count1 (Int.toNat n) o6) (Int.toNat n) o11) = List.length (List.set count1 (Int.toNat n) o6) → getElem! (List.set (List.set count1 (Int.toNat n) o6) (Int.toNat n) o11) ∘ Int.toNat = Function.update (getElem! (List.set count1 (Int.toNat n) o6) ∘ Int.toNat) n o11 → ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length (List.set sets1 (Int.toNat n) o8))) ∧ (let o12 : Finset (List color) := (List.set sets1 (Int.toNat n) o8)[Int.toNat n]!; (∀(x : List color), x ∈ o12 → ¬x ∈ sr) ∧ (let o13 : Finset (List color) := o12 ∪ sr; Int.ofNat (Finset.card o13) = Int.ofNat (Finset.card o12) + Int.ofNat (Finset.card sr) → ((0 : ℤ) ≤ n ∧ n < Int.ofNat (List.length (List.set sets1 (Int.toNat n) o8))) ∧ (List.length (List.set (List.set sets1 (Int.toNat n) o8) (Int.toNat n) o13) = List.length (List.set sets1 (Int.toNat n) o8) → getElem! (List.set (List.set sets1 (Int.toNat n) o8) (Int.toNat n) o13) ∘ Int.toNat = Function.update (getElem! (List.set sets1 (Int.toNat n) o8) ∘ Int.toNat) n o13 → (∀(c : List color), (0 : ℤ) ≤ Int.ofNat (List.length c) ∧ Int.ofNat (List.length c) < n + (1 : ℤ) → valid c → c ∈ (List.set (List.set sets1 (Int.toNat n) o8) (Int.toNat n) o13)[List.length c]!) ∧ (∀(c : List color) (i : ℤ), (0 : ℤ) ≤ i ∧ i < n + (1 : ℤ) → c ∈ (List.set (List.set sets1 (Int.toNat n) o8) (Int.toNat n) o13)[Int.toNat i]! → Int.ofNat (List.length c) = i ∧ valid c) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n + (1 : ℤ) → (List.set (List.set count1 (Int.toNat n) o6) (Int.toNat n) o11)[Int.toNat i]! = Int.ofNat (Finset.card ((List.set (List.set sets1 (Int.toNat n) o8) (Int.toNat n) o13)[Int.toNat i]!)))))))))))))))))))) ∧ ((∀(c : List color), (0 : ℤ) ≤ Int.ofNat (List.length c) ∧ Int.ofNat (List.length c) < (50 : ℤ) + (1 : ℤ) → valid c → c ∈ sets1[List.length c]!) ∧ (∀(c : List color) (i : ℤ), (0 : ℤ) ≤ i ∧ i < (50 : ℤ) + (1 : ℤ) → c ∈ sets1[Int.toNat i]! → Int.ofNat (List.length c) = i ∧ valid c) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (50 : ℤ) + (1 : ℤ) → count1[Int.toNat i]! = Int.ofNat (Finset.card (sets1[Int.toNat i]!))) → (Int.ofNat (List.length count1) = (51 : ℤ) ∧ (51 : ℤ) = Int.ofNat (List.length sets1)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i ≤ (50 : ℤ) → (∀(c : List color), Int.ofNat (List.length c) = i → valid c = (c ∈ sets1[Int.toNat i]!))) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (50 : ℤ) → count1[Int.toNat i]! = Int.ofNat (Finset.card (sets1[Int.toNat i]!)))))) ∧ ((50 : ℤ) + (1 : ℤ) < (4 : ℤ) → (Int.ofNat (List.length (List.set (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)) (3 : ℕ) (2 : ℤ))) = (51 : ℤ) ∧ (51 : ℤ) = Int.ofNat (List.length (List.set (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) (3 : ℕ) o4))) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i ≤ (50 : ℤ) → (∀(c : List color), Int.ofNat (List.length c) = i → valid c = (c ∈ (List.set (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) (3 : ℕ) o4)[Int.toNat i]!))) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (50 : ℤ) → (List.set (List.set (List.set (List.set count (0 : ℕ) (1 : ℤ)) (1 : ℕ) (1 : ℤ)) (2 : ℕ) (1 : ℤ)) (3 : ℕ) (2 : ℤ))[Int.toNat i]! = Int.ofNat (Finset.card ((List.set (List.set (List.set (List.set sets (0 : ℕ) o1) (1 : ℕ) o2) (2 : ℕ) o3) (3 : ℕ) o4)[Int.toNat i]!))))))))))))))))))
  := sorry
end verifythis_2018_le_rouge_et_le_noir_1_ColoredTiles_enumqtvc
