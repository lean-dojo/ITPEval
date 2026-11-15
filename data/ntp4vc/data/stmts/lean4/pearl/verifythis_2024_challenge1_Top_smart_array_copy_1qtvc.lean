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

namespace verifythis_2024_challenge1_Top_smart_array_copy_1qtvc
noncomputable def permutation (l : ℤ) (p : List ℤ) := ((0 : ℤ) ≤ l ∧ l ≤ Int.ofNat (List.length p)) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < l → (0 : ℤ) ≤ p[Int.toNat i]! ∧ p[Int.toNat i]! < l) ∧ (∀(i : ℤ) (j : ℤ), (0 : ℤ) ≤ i ∧ i < l → (0 : ℤ) ≤ j ∧ j < l → ¬i = j → ¬p[Int.toNat i]! = p[Int.toNat j]!)
noncomputable def permutation_pair (l : ℤ) (p : List ℤ) (invp : List ℤ) := permutation l p ∧ permutation l invp ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < l → p[Int.toNat (invp[Int.toNat i]!)]! = i) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < l → invp[Int.toNat (p[Int.toNat i]!)]! = i)
axiom identity : ℤ -> List ℤ
axiom identity'spec'1 (l : ℤ) (fact0 : (0 : ℤ) < l) : Int.ofNat (List.length (identity l)) = l
axiom identity'spec'0 (l : ℤ) (i : ℤ) (fact0 : (0 : ℤ) < l) (fact1 : (0 : ℤ) ≤ i) (fact2 : i < l) : (identity l)[Int.toNat i]! = i
axiom identity'spec (l : ℤ) (fact0 : (0 : ℤ) < l) : permutation_pair l (identity l) (identity l)
axiom elt : Type
axiom inhabited_axiom_elt : Inhabited elt
attribute [instance] inhabited_axiom_elt
noncomputable def valid_chunk (a : List elt) (ofs : ℤ) (len : ℤ) := (0 : ℤ) ≤ ofs ∧ ofs ≤ ofs + len ∧ ofs + len ≤ Int.ofNat (List.length a)
noncomputable def copy (src : List elt) (dst : List elt) (ofs : ℤ) (len : ℤ) := valid_chunk src ofs len ∧ List.length src = List.length dst ∧ (∀(i : ℤ), ofs ≤ i ∧ i < ofs + len → dst[Int.toNat i]! = src[Int.toNat i]!)
noncomputable def copy_to (src : List elt) (dst : List elt) (ofss : ℤ) (ofsd : ℤ) (len : ℤ) := valid_chunk src ofss len ∧ valid_chunk dst ofsd len ∧ List.length src = List.length dst ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < len → dst[Int.toNat (ofsd + i)]! = src[Int.toNat (ofss + i)]!) ∧ (∀(i : ℤ), ofsd ≤ i ∧ i < ofsd + len → dst[Int.toNat i]! = src[Int.toNat (i + (ofss - ofsd))]!)
noncomputable def copy_perm (src : List elt) (dst : List elt) (size : ℤ) (p : List ℤ) (invp : List ℤ) := valid_chunk src (0 : ℤ) size ∧ List.length src = List.length dst ∧ permutation_pair size p invp ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < size → (0 : ℤ) ≤ p[Int.toNat i]! ∧ p[Int.toNat i]! < size) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < size → (0 : ℤ) ≤ invp[Int.toNat i]! ∧ invp[Int.toNat i]! < size) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < size → dst[Int.toNat i]! = src[Int.toNat (p[Int.toNat i]!)]!) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < size → src[Int.toNat i]! = dst[Int.toNat (invp[Int.toNat i]!)]!)
noncomputable def copy_subsegment (src : List elt) (dst : List elt) (s : ℤ) (k : ℤ) (l : ℤ) (j : ℤ) (sigma : List ℤ) (tau : List ℤ) (p : List ℤ) (invp : List ℤ) := let start : ℤ := s * (k * l); let starts : ℤ := start + sigma[Int.toNat j]! * k; let startd : ℤ := start + tau[Int.toNat (sigma[Int.toNat j]!)]! * k; copy_to src dst starts startd k ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < k → p[Int.toNat (startd + i)]! = starts + i) ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < k → invp[Int.toNat (starts + i)]! = startd + i)
noncomputable def frame {α : Type} [Inhabited α] (a1 : List α) (a2 : List α) (ofs : ℤ) (len : ℤ) := List.length a2 = List.length a1 ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < ofs → a2[Int.toNat i]! = a1[Int.toNat i]!) ∧ (∀(i : ℤ), ofs + len ≤ i ∧ i < Int.ofNat (List.length a2) → a2[Int.toNat i]! = a1[Int.toNat i]!)
theorem smart_array_copy_1'vc (src : List elt) (dst : List elt) (k : ℤ) (l : ℤ) (q : ℤ) (r : ℤ) (fact0 : List.length src = List.length dst) (fact1 : (0 : ℤ) < Int.ofNat (List.length dst)) (fact2 : (0 : ℤ) < k) (fact3 : (0 : ℤ) < l) (fact4 : (0 : ℤ) ≤ q) (fact5 : (0 : ℤ) ≤ r) (fact6 : r < k * l) (fact7 : Int.ofNat (List.length dst) = q * k * l + r) : (0 : ℤ) < Int.ofNat (List.length dst) ∧ (let p : List ℤ := identity (Int.ofNat (List.length dst)); List.length p = List.length dst ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length dst) → p[Int.toNat i]! = i) ∧ permutation_pair (Int.ofNat (List.length dst)) p p → (0 : ℤ) < Int.ofNat (List.length dst) ∧ (let invp : List ℤ := identity (Int.ofNat (List.length dst)); List.length invp = List.length dst ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length dst) → invp[Int.toNat i]! = i) ∧ permutation_pair (Int.ofNat (List.length dst)) invp invp → (let m : ℤ := k * l; let o1 : ℤ := q - (1 : ℤ); ((0 : ℤ) ≤ o1 + (1 : ℤ) → (permutation_pair ((0 : ℤ) * m) p invp ∧ copy_perm src dst ((0 : ℤ) * m) p invp) ∧ (∀(invp1 : List ℤ) (p1 : List ℤ) (dst1 : List elt), List.length invp1 = List.length invp → List.length p1 = List.length p → List.length dst1 = List.length dst → (∀(s : ℤ), ((0 : ℤ) ≤ s ∧ s ≤ o1) ∧ permutation_pair (s * m) p1 invp1 ∧ copy_perm src dst1 (s * m) p1 invp1 → (let start : ℤ := s * m; (0 : ℤ) < l ∧ (∀(sigma : List ℤ) (invsigma : List ℤ), (List.length sigma = List.length invsigma ∧ Int.ofNat (List.length invsigma) = l) ∧ permutation_pair l sigma invsigma → (0 : ℤ) < l ∧ (∀(tau : List ℤ) (invtau : List ℤ), (List.length tau = List.length invtau ∧ Int.ofNat (List.length invtau) = l) ∧ permutation_pair l tau invtau → (let o2 : ℤ := l - (1 : ℤ); ((0 : ℤ) ≤ o2 + (1 : ℤ) → (permutation_pair (s * m) p1 invp1 ∧ copy_perm src dst1 (s * m) p1 invp1 ∧ (∀(j' : ℤ), (0 : ℤ) ≤ j' ∧ j' < (0 : ℤ) → copy_subsegment src dst1 s k l j' sigma tau p1 invp1)) ∧ (∀(invp2 : List ℤ) (p2 : List ℤ) (dst2 : List elt), List.length invp2 = List.length invp1 → List.length p2 = List.length p1 → List.length dst2 = List.length dst1 → (∀(j : ℤ), ((0 : ℤ) ≤ j ∧ j ≤ o2) ∧ permutation_pair (s * m) p2 invp2 ∧ copy_perm src dst2 (s * m) p2 invp2 ∧ (∀(j' : ℤ), (0 : ℤ) ≤ j' ∧ j' < j → copy_subsegment src dst2 s k l j' sigma tau p2 invp2) → ((0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length sigma)) ∧ (let startsrc : ℤ := start + sigma[Int.toNat j]! * k; ((0 : ℤ) ≤ j ∧ j < Int.ofNat (List.length sigma)) ∧ (let o3 : ℤ := sigma[Int.toNat j]!; ((0 : ℤ) ≤ o3 ∧ o3 < Int.ofNat (List.length tau)) ∧ (let startdst : ℤ := start + tau[Int.toNat o3]! * k; let o4 : ℤ := k - (1 : ℤ); ((0 : ℤ) ≤ o4 + (1 : ℤ) → (frame dst2 dst2 startdst k ∧ frame p2 p2 startdst k ∧ frame invp2 invp2 startsrc k ∧ permutation_pair (s * m) p2 invp2 ∧ copy_perm src dst2 (s * m) p2 invp2 ∧ copy_to src dst2 startsrc startdst (0 : ℤ) ∧ (∀(i' : ℤ), (0 : ℤ) ≤ i' ∧ i' < (0 : ℤ) → p2[Int.toNat (startdst + i')]! = startsrc + i') ∧ (∀(i' : ℤ), (0 : ℤ) ≤ i' ∧ i' < (0 : ℤ) → invp2[Int.toNat (startsrc + i')]! = startdst + i') ∧ (∀(j' : ℤ), (0 : ℤ) ≤ j' ∧ j' < j → copy_subsegment src dst2 s k l j' sigma tau p2 invp2)) ∧ (∀(invp3 : List ℤ) (p3 : List ℤ) (dst3 : List elt), List.length invp3 = List.length invp2 → List.length p3 = List.length p2 → List.length dst3 = List.length dst2 → (∀(i : ℤ), ((0 : ℤ) ≤ i ∧ i ≤ o4) ∧ frame dst2 dst3 startdst k ∧ frame p2 p3 startdst k ∧ frame invp2 invp3 startsrc k ∧ permutation_pair (s * m) p3 invp3 ∧ copy_perm src dst3 (s * m) p3 invp3 ∧ copy_to src dst3 startsrc startdst i ∧ (∀(i' : ℤ), (0 : ℤ) ≤ i' ∧ i' < i → p3[Int.toNat (startdst + i')]! = startsrc + i') ∧ (∀(i' : ℤ), (0 : ℤ) ≤ i' ∧ i' < i → invp3[Int.toNat (startsrc + i')]! = startdst + i') ∧ (∀(j' : ℤ), (0 : ℤ) ≤ j' ∧ j' < j → copy_subsegment src dst3 s k l j' sigma tau p3 invp3) → (let o5 : ℤ := startsrc + i; ((0 : ℤ) ≤ o5 ∧ o5 < Int.ofNat (List.length src)) ∧ (let o6 : elt := src[Int.toNat o5]!; let o7 : ℤ := startdst + i; ((0 : ℤ) ≤ o7 ∧ o7 < Int.ofNat (List.length dst3)) ∧ (List.length (List.set dst3 (Int.toNat o7) o6) = List.length dst3 → getElem! (List.set dst3 (Int.toNat o7) o6) ∘ Int.toNat = Function.update (getElem! dst3 ∘ Int.toNat) o7 o6 → (let o8 : ℤ := startsrc + i; let o9 : ℤ := startdst + i; ((0 : ℤ) ≤ o9 ∧ o9 < Int.ofNat (List.length p3)) ∧ (List.length (List.set p3 (Int.toNat o9) o8) = List.length p3 → getElem! (List.set p3 (Int.toNat o9) o8) ∘ Int.toNat = Function.update (getElem! p3 ∘ Int.toNat) o9 o8 → (let o10 : ℤ := startdst + i; let o11 : ℤ := startsrc + i; ((0 : ℤ) ≤ o11 ∧ o11 < Int.ofNat (List.length invp3)) ∧ (List.length (List.set invp3 (Int.toNat o11) o10) = List.length invp3 → getElem! (List.set invp3 (Int.toNat o11) o10) ∘ Int.toNat = Function.update (getElem! invp3 ∘ Int.toNat) o11 o10 → frame dst2 (List.set dst3 (Int.toNat o7) o6) startdst k ∧ frame p2 (List.set p3 (Int.toNat o9) o8) startdst k ∧ frame invp2 (List.set invp3 (Int.toNat o11) o10) startsrc k ∧ permutation_pair (s * m) (List.set p3 (Int.toNat o9) o8) (List.set invp3 (Int.toNat o11) o10) ∧ copy_perm src (List.set dst3 (Int.toNat o7) o6) (s * m) (List.set p3 (Int.toNat o9) o8) (List.set invp3 (Int.toNat o11) o10) ∧ copy_to src (List.set dst3 (Int.toNat o7) o6) startsrc startdst (i + (1 : ℤ)) ∧ (∀(i' : ℤ), (0 : ℤ) ≤ i' ∧ i' < i + (1 : ℤ) → (List.set p3 (Int.toNat o9) o8)[Int.toNat (startdst + i')]! = startsrc + i') ∧ (∀(i' : ℤ), (0 : ℤ) ≤ i' ∧ i' < i + (1 : ℤ) → (List.set invp3 (Int.toNat o11) o10)[Int.toNat (startsrc + i')]! = startdst + i') ∧ (∀(j' : ℤ), (0 : ℤ) ≤ j' ∧ j' < j → copy_subsegment src (List.set dst3 (Int.toNat o7) o6) s k l j' sigma tau (List.set p3 (Int.toNat o9) o8) (List.set invp3 (Int.toNat o11) o10)))))))))) ∧ (frame dst2 dst3 startdst k ∧ frame p2 p3 startdst k ∧ frame invp2 invp3 startsrc k ∧ permutation_pair (s * m) p3 invp3 ∧ copy_perm src dst3 (s * m) p3 invp3 ∧ copy_to src dst3 startsrc startdst (o4 + (1 : ℤ)) ∧ (∀(i' : ℤ), (0 : ℤ) ≤ i' ∧ i' < o4 + (1 : ℤ) → p3[Int.toNat (startdst + i')]! = startsrc + i') ∧ (∀(i' : ℤ), (0 : ℤ) ≤ i' ∧ i' < o4 + (1 : ℤ) → invp3[Int.toNat (startsrc + i')]! = startdst + i') ∧ (∀(j' : ℤ), (0 : ℤ) ≤ j' ∧ j' < j → copy_subsegment src dst3 s k l j' sigma tau p3 invp3) → permutation_pair (s * m) p3 invp3 ∧ copy_perm src dst3 (s * m) p3 invp3 ∧ (∀(j' : ℤ), (0 : ℤ) ≤ j' ∧ j' < j + (1 : ℤ) → copy_subsegment src dst3 s k l j' sigma tau p3 invp3)))) ∧ (o4 + (1 : ℤ) < (0 : ℤ) → permutation_pair (s * m) p2 invp2 ∧ copy_perm src dst2 (s * m) p2 invp2 ∧ (∀(j' : ℤ), (0 : ℤ) ≤ j' ∧ j' < j + (1 : ℤ) → copy_subsegment src dst2 s k l j' sigma tau p2 invp2)))))) ∧ (permutation_pair (s * m) p2 invp2 ∧ copy_perm src dst2 (s * m) p2 invp2 ∧ (∀(j' : ℤ), (0 : ℤ) ≤ j' ∧ j' < o2 + (1 : ℤ) → copy_subsegment src dst2 s k l j' sigma tau p2 invp2) → permutation_pair ((s + (1 : ℤ)) * m) p2 invp2 ∧ copy_perm src dst2 ((s + (1 : ℤ)) * m) p2 invp2))) ∧ (o2 + (1 : ℤ) < (0 : ℤ) → permutation_pair ((s + (1 : ℤ)) * m) p1 invp1 ∧ copy_perm src dst1 ((s + (1 : ℤ)) * m) p1 invp1)))))) ∧ (permutation_pair ((o1 + (1 : ℤ)) * m) p1 invp1 ∧ copy_perm src dst1 ((o1 + (1 : ℤ)) * m) p1 invp1 → (let last : ℤ := q * m; let o2 : ℤ := r - (1 : ℤ); ((0 : ℤ) ≤ o2 + (1 : ℤ) → (permutation_pair (last + (0 : ℤ)) p1 invp1 ∧ copy_perm src dst1 (last + (0 : ℤ)) p1 invp1) ∧ (∀(invp2 : List ℤ) (p2 : List ℤ) (dst2 : List elt), List.length invp2 = List.length invp1 → List.length p2 = List.length p1 → List.length dst2 = List.length dst1 → (∀(i : ℤ), ((0 : ℤ) ≤ i ∧ i ≤ o2) ∧ permutation_pair (last + i) p2 invp2 ∧ copy_perm src dst2 (last + i) p2 invp2 → (let o3 : ℤ := last + i; ((0 : ℤ) ≤ o3 ∧ o3 < Int.ofNat (List.length src)) ∧ (let o4 : elt := src[Int.toNat o3]!; let o5 : ℤ := last + i; ((0 : ℤ) ≤ o5 ∧ o5 < Int.ofNat (List.length dst2)) ∧ (List.length (List.set dst2 (Int.toNat o5) o4) = List.length dst2 → getElem! (List.set dst2 (Int.toNat o5) o4) ∘ Int.toNat = Function.update (getElem! dst2 ∘ Int.toNat) o5 o4 → (let o6 : ℤ := last + i; let o7 : ℤ := last + i; ((0 : ℤ) ≤ o7 ∧ o7 < Int.ofNat (List.length p2)) ∧ (List.length (List.set p2 (Int.toNat o7) o6) = List.length p2 → getElem! (List.set p2 (Int.toNat o7) o6) ∘ Int.toNat = Function.update (getElem! p2 ∘ Int.toNat) o7 o6 → (let o8 : ℤ := last + i; let o9 : ℤ := last + i; ((0 : ℤ) ≤ o9 ∧ o9 < Int.ofNat (List.length invp2)) ∧ (List.length (List.set invp2 (Int.toNat o9) o8) = List.length invp2 → getElem! (List.set invp2 (Int.toNat o9) o8) ∘ Int.toNat = Function.update (getElem! invp2 ∘ Int.toNat) o9 o8 → permutation_pair (last + (i + (1 : ℤ))) (List.set p2 (Int.toNat o7) o6) (List.set invp2 (Int.toNat o9) o8) ∧ copy_perm src (List.set dst2 (Int.toNat o5) o4) (last + (i + (1 : ℤ))) (List.set p2 (Int.toNat o7) o6) (List.set invp2 (Int.toNat o9) o8))))))))) ∧ (permutation_pair (last + (o2 + (1 : ℤ))) p2 invp2 ∧ copy_perm src dst2 (last + (o2 + (1 : ℤ))) p2 invp2 → copy_perm src dst2 (Int.ofNat (List.length dst)) p2 invp2))) ∧ (o2 + (1 : ℤ) < (0 : ℤ) → copy_perm src dst1 (Int.ofNat (List.length dst)) p1 invp1))))) ∧ (o1 + (1 : ℤ) < (0 : ℤ) → (let last : ℤ := q * m; let o2 : ℤ := r - (1 : ℤ); ((0 : ℤ) ≤ o2 + (1 : ℤ) → (permutation_pair (last + (0 : ℤ)) p invp ∧ copy_perm src dst (last + (0 : ℤ)) p invp) ∧ (∀(invp1 : List ℤ) (p1 : List ℤ) (dst1 : List elt), List.length invp1 = List.length invp → List.length p1 = List.length p → List.length dst1 = List.length dst → (∀(i : ℤ), ((0 : ℤ) ≤ i ∧ i ≤ o2) ∧ permutation_pair (last + i) p1 invp1 ∧ copy_perm src dst1 (last + i) p1 invp1 → (let o3 : ℤ := last + i; ((0 : ℤ) ≤ o3 ∧ o3 < Int.ofNat (List.length src)) ∧ (let o4 : elt := src[Int.toNat o3]!; let o5 : ℤ := last + i; ((0 : ℤ) ≤ o5 ∧ o5 < Int.ofNat (List.length dst1)) ∧ (List.length (List.set dst1 (Int.toNat o5) o4) = List.length dst1 → getElem! (List.set dst1 (Int.toNat o5) o4) ∘ Int.toNat = Function.update (getElem! dst1 ∘ Int.toNat) o5 o4 → (let o6 : ℤ := last + i; let o7 : ℤ := last + i; ((0 : ℤ) ≤ o7 ∧ o7 < Int.ofNat (List.length p1)) ∧ (List.length (List.set p1 (Int.toNat o7) o6) = List.length p1 → getElem! (List.set p1 (Int.toNat o7) o6) ∘ Int.toNat = Function.update (getElem! p1 ∘ Int.toNat) o7 o6 → (let o8 : ℤ := last + i; let o9 : ℤ := last + i; ((0 : ℤ) ≤ o9 ∧ o9 < Int.ofNat (List.length invp1)) ∧ (List.length (List.set invp1 (Int.toNat o9) o8) = List.length invp1 → getElem! (List.set invp1 (Int.toNat o9) o8) ∘ Int.toNat = Function.update (getElem! invp1 ∘ Int.toNat) o9 o8 → permutation_pair (last + (i + (1 : ℤ))) (List.set p1 (Int.toNat o7) o6) (List.set invp1 (Int.toNat o9) o8) ∧ copy_perm src (List.set dst1 (Int.toNat o5) o4) (last + (i + (1 : ℤ))) (List.set p1 (Int.toNat o7) o6) (List.set invp1 (Int.toNat o9) o8))))))))) ∧ (permutation_pair (last + (o2 + (1 : ℤ))) p1 invp1 ∧ copy_perm src dst1 (last + (o2 + (1 : ℤ))) p1 invp1 → copy_perm src dst1 (Int.ofNat (List.length dst)) p1 invp1))) ∧ (o2 + (1 : ℤ) < (0 : ℤ) → copy_perm src dst (Int.ofNat (List.length dst)) p invp))))))
  := sorry
end verifythis_2024_challenge1_Top_smart_array_copy_1qtvc
