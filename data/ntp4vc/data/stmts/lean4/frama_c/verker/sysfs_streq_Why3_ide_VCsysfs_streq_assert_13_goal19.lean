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

namespace Qed
axiom match_bool :  {α : Type} -> [Inhabited α] -> Bool -> α -> α -> α
axiom eqb :  {α : Type} -> [Inhabited α] -> α -> α -> Bool
axiom eqb1 {α : Type} [Inhabited α] (x : α) (y : α) : (eqb x y = true) = (x = y)
axiom neqb :  {α : Type} -> [Inhabited α] -> α -> α -> Bool
axiom neqb1 {α : Type} [Inhabited α] (x : α) (y : α) : (neqb x y = true) = (¬x = y)
axiom zlt : ℤ -> ℤ -> Bool
axiom zleq : ℤ -> ℤ -> Bool
axiom zlt1 (x : ℤ) (y : ℤ) : (zlt x y = true) = (x < y)
axiom zleq1 (x : ℤ) (y : ℤ) : (zleq x y = true) = (x ≤ y)
axiom rlt : ℝ -> ℝ -> Bool
axiom rleq : ℝ -> ℝ -> Bool
axiom rlt1 (x : ℝ) (y : ℝ) : (rlt x y = true) = (x < y)
axiom rleq1 (x : ℝ) (y : ℝ) : (rleq x y = true) = (x ≤ y)
axiom c_euclidian (d : ℤ) (n : ℤ) (fact0 : ¬d = (0 : ℤ)) : n = Int.tdiv n d * d + Int.tmod n d
axiom cdiv_cases (n : ℤ) (d : ℤ) : (n ≤ (0 : ℤ) → (0 : ℤ) < d → Int.tdiv n d = -Int.tdiv (-n) d) ∧ ((0 : ℤ) ≤ n → d < (0 : ℤ) → Int.tdiv n d = -Int.tdiv n (-d)) ∧ (n ≤ (0 : ℤ) → d < (0 : ℤ) → Int.tdiv n d = Int.tdiv (-n) (-d))
axiom cmod_cases (n : ℤ) (d : ℤ) : (n ≤ (0 : ℤ) → (0 : ℤ) < d → Int.tmod n d = -Int.tmod (-n) d) ∧ ((0 : ℤ) ≤ n → d < (0 : ℤ) → Int.tmod n d = Int.tmod n (-d)) ∧ (n ≤ (0 : ℤ) → d < (0 : ℤ) → Int.tmod n d = -Int.tmod (-n) (-d))
axiom cmod_remainder (n : ℤ) (d : ℤ) : ((0 : ℤ) ≤ n → (0 : ℤ) < d → (0 : ℤ) ≤ Int.tmod n d ∧ Int.tmod n d < d) ∧ (n ≤ (0 : ℤ) → (0 : ℤ) < d → -d < Int.tmod n d ∧ Int.tmod n d ≤ (0 : ℤ)) ∧ ((0 : ℤ) ≤ n → d < (0 : ℤ) → (0 : ℤ) ≤ Int.tmod n d ∧ Int.tmod n d < -d) ∧ (n ≤ (0 : ℤ) → d < (0 : ℤ) → d < Int.tmod n d ∧ Int.tmod n d ≤ (0 : ℤ))
axiom cdiv_neutral (a : ℤ) : Int.tdiv a (1 : ℤ) = a
axiom cdiv_inv (a : ℤ) (fact0 : ¬a = (0 : ℤ)) : Int.tdiv a a = (1 : ℤ)
end Qed
namespace Axiomatic3
end Axiomatic3
namespace Memory
structure addr where
  base : ℤ
  offset : ℤ
axiom inhabited_axiom_addr : Inhabited addr
attribute [instance] inhabited_axiom_addr
axiom addr_le : addr -> addr -> Prop
axiom addr_lt : addr -> addr -> Prop
axiom addr_le_bool : addr -> addr -> Bool
axiom addr_lt_bool : addr -> addr -> Bool
axiom addr_le_def (p : addr) (q : addr) (fact0 : addr.base p = addr.base q) : addr_le p q = (addr.offset p ≤ addr.offset q)
axiom addr_lt_def (p : addr) (q : addr) (fact0 : addr.base p = addr.base q) : addr_lt p q = (addr.offset p < addr.offset q)
axiom addr_le_bool_def (p : addr) (q : addr) : addr_le p q = (addr_le_bool p q = true)
axiom addr_lt_bool_def (p : addr) (q : addr) : addr_lt p q = (addr_lt_bool p q = true)
noncomputable def shift (p : addr) (k : ℤ) := addr.mk (addr.base p) (addr.offset p + k)
noncomputable def shift_sint16 (p : addr) (k : ℤ) := shift p ((2 : ℤ) * k)
noncomputable def shift_sint32 (p : addr) (k : ℤ) := shift p ((4 : ℤ) * k)
noncomputable def shift_sint64 (p : addr) (k : ℤ) := shift p ((8 : ℤ) * k)
noncomputable def shift_uint16 (p : addr) (k : ℤ) := shift p ((2 : ℤ) * k)
noncomputable def shift_uint32 (p : addr) (k : ℤ) := shift p ((4 : ℤ) * k)
noncomputable def shift_uint64 (p : addr) (k : ℤ) := shift p ((8 : ℤ) * k)
noncomputable def shift_ptr (p : addr) (k : ℤ) := shift p ((8 : ℤ) * k)
noncomputable def included (p : addr) (a : ℤ) (q : addr) (b : ℤ) := (0 : ℤ) < a → (0 : ℤ) ≤ b ∧ addr.base p = addr.base q ∧ addr.offset q ≤ addr.offset p ∧ addr.offset p + a ≤ addr.offset q + b
noncomputable def separated (p : addr) (a : ℤ) (q : addr) (b : ℤ) := a ≤ (0 : ℤ) ∨ b ≤ (0 : ℤ) ∨ ¬addr.base p = addr.base q ∨ addr.offset q + b ≤ addr.offset p ∨ addr.offset p + a ≤ addr.offset q
noncomputable def eqmem {α : Type} [Inhabited α] (m1 : addr -> α) (m2 : addr -> α) (p : addr) (a : ℤ) := ∀(q : addr), included q (1 : ℤ) p a → m1 q = m2 q
axiom havoc :  {α : Type} -> [Inhabited α] -> (addr -> α) -> (addr -> α) -> addr -> ℤ -> addr -> α
noncomputable def valid_rw (m : ℤ -> ℤ) (p : addr) (n : ℤ) := (0 : ℤ) < n → (0 : ℤ) < addr.base p ∧ (0 : ℤ) ≤ addr.offset p ∧ addr.offset p + n ≤ m (addr.base p)
noncomputable def valid_rd (m : ℤ -> ℤ) (p : addr) (n : ℤ) := (0 : ℤ) < n → ¬(0 : ℤ) = addr.base p ∧ (0 : ℤ) ≤ addr.offset p ∧ addr.offset p + n ≤ m (addr.base p)
noncomputable def invalid (m : ℤ -> ℤ) (p : addr) (n : ℤ) := (0 : ℤ) < n → m (addr.base p) ≤ addr.offset p ∨ addr.offset p + n ≤ (0 : ℤ)
axiom valid_rw_rd (m : ℤ -> ℤ) (p : addr) (n : ℤ) (fact0 : valid_rw m p n) : valid_rd m p n
axiom valid_string (p : addr) (m : ℤ -> ℤ) (fact0 : addr.base p < (0 : ℤ)) (fact1 : (0 : ℤ) ≤ addr.offset p) (fact2 : addr.offset p < m (addr.base p)) : valid_rd m p (1 : ℤ) ∧ ¬valid_rw m p (1 : ℤ)
axiom separated_1 (p : addr) (a : ℤ) (q : addr) (b : ℤ) (i : ℤ) (j : ℤ) (fact0 : separated p a q b) (fact1 : addr.offset p ≤ i) (fact2 : i < addr.offset p + a) (fact3 : addr.offset q ≤ j) (fact4 : j < addr.offset q + b) : ¬addr.mk (addr.base p) i = addr.mk (addr.base q) j
axiom region : ℤ -> ℤ
axiom linked : (ℤ -> ℤ) -> Prop
axiom sconst : (addr -> ℤ) -> Prop
noncomputable def framed (m : addr -> addr) := ∀(p : addr), region (addr.base (m p)) ≤ (0 : ℤ)
axiom separated_included (a : ℤ) (b : ℤ) (p : addr) (q : addr) (fact0 : (0 : ℤ) < a) (fact1 : (0 : ℤ) < b) (fact2 : separated p a q b) : ¬included p a q b
axiom included_trans (p : addr) (a : ℤ) (q : addr) (b : ℤ) (r : addr) (c : ℤ) (fact0 : included p a q b) (fact1 : included q b r c) : included p a r c
axiom separated_trans (p : addr) (a : ℤ) (q : addr) (b : ℤ) (r : addr) (c : ℤ) (fact0 : included p a q b) (fact1 : separated q b r c) : separated p a r c
axiom separated_sym (p : addr) (a : ℤ) (q : addr) (b : ℤ) : separated p a q b = separated q b p a
axiom eqmem_included {α : Type} [Inhabited α] (p : addr) (a : ℤ) (q : addr) (b : ℤ) (m1 : addr -> α) (m2 : addr -> α) (fact0 : included p a q b) (fact1 : eqmem m1 m2 q b) : eqmem m1 m2 p a
axiom eqmem_sym {α : Type} [Inhabited α] (m1 : addr -> α) (m2 : addr -> α) (p : addr) (a : ℤ) (fact0 : eqmem m1 m2 p a) : eqmem m2 m1 p a
axiom havoc_access {α : Type} [Inhabited α] (m0 : addr -> α) (m1 : addr -> α) (p : addr) (a : ℤ) (q : addr) : havoc m0 m1 p a q = (if separated q (1 : ℤ) p a then m1 q else m0 q)
axiom int_of_addr : addr -> ℤ
axiom addr_of_int : ℤ -> addr
axiom base_offset : ℤ -> ℤ
axiom base_index : ℤ -> ℤ
axiom int_of_addr_bijection (a : ℤ) : int_of_addr (addr_of_int a) = a
axiom addr_of_int_bijection (p : addr) : addr_of_int (int_of_addr p) = p
axiom addr_of_null : int_of_addr (addr.mk (0 : ℤ) (0 : ℤ)) = (0 : ℤ)
axiom base_offset_zero : base_offset (0 : ℤ) = (0 : ℤ)
axiom base_offset_inj (i : ℤ) : base_index (base_offset i) = i
axiom base_offset_monotonic (i : ℤ) (j : ℤ) (fact0 : i < j) : base_offset i < base_offset j
end Memory
namespace Compound
end Compound
namespace Cint
noncomputable def is_bool (x : ℤ) := x = (0 : ℤ) ∨ x = (1 : ℤ)
noncomputable def is_uint8 (x : ℤ) := (0 : ℤ) ≤ x ∧ x < (256 : ℤ)
noncomputable def is_sint8 (x : ℤ) := -(128 : ℤ) ≤ x ∧ x < (128 : ℤ)
noncomputable def is_uint16 (x : ℤ) := (0 : ℤ) ≤ x ∧ x < (65536 : ℤ)
noncomputable def is_sint16 (x : ℤ) := -(32768 : ℤ) ≤ x ∧ x < (32768 : ℤ)
noncomputable def is_uint32 (x : ℤ) := (0 : ℤ) ≤ x ∧ x < (4294967296 : ℤ)
noncomputable def is_sint32 (x : ℤ) := -(2147483648 : ℤ) ≤ x ∧ x < (2147483648 : ℤ)
noncomputable def is_uint64 (x : ℤ) := (0 : ℤ) ≤ x ∧ x < (18446744073709551616 : ℤ)
noncomputable def is_sint64 (x : ℤ) := -(9223372036854775808 : ℤ) ≤ x ∧ x < (9223372036854775808 : ℤ)
axiom is_bool0 : is_bool (0 : ℤ)
axiom is_bool1 : is_bool (1 : ℤ)
noncomputable def to_bool (x : ℤ) := if x = (0 : ℤ) then (0 : ℤ) else (1 : ℤ)
axiom to_uint8 : ℤ -> ℤ
axiom to_sint8 : ℤ -> ℤ
axiom to_uint16 : ℤ -> ℤ
axiom to_sint16 : ℤ -> ℤ
axiom to_uint32 : ℤ -> ℤ
axiom to_sint32 : ℤ -> ℤ
axiom to_uint64 : ℤ -> ℤ
axiom to_sint64 : ℤ -> ℤ
axiom two_power_abs : ℤ -> ℤ
axiom two_power_abs_is_positive (n : ℤ) : (0 : ℤ) < two_power_abs n
axiom two_power_abs_plus_pos (n : ℤ) (m : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ m) : two_power_abs (n + m) = two_power_abs n * two_power_abs m
axiom two_power_abs_plus_one (n : ℤ) (fact0 : (0 : ℤ) ≤ n) : two_power_abs (n + (1 : ℤ)) = (2 : ℤ) * two_power_abs n
noncomputable def is_uint (n : ℤ) (x : ℤ) := (0 : ℤ) ≤ x ∧ x < two_power_abs n
noncomputable def is_sint (n : ℤ) (x : ℤ) := -two_power_abs n ≤ x ∧ x < two_power_abs n
axiom to_uint : ℤ -> ℤ -> ℤ
axiom to_sint : ℤ -> ℤ -> ℤ
axiom is_to_uint (n : ℤ) (x : ℤ) : is_uint n (to_uint n x)
axiom is_to_sint (n : ℤ) (x : ℤ) : is_sint n (to_sint n x)
axiom is_to_uint8 (x : ℤ) : is_uint8 (to_uint8 x)
axiom is_to_sint8 (x : ℤ) : is_sint8 (to_sint8 x)
axiom is_to_uint16 (x : ℤ) : is_uint16 (to_uint16 x)
axiom is_to_sint16 (x : ℤ) : is_sint16 (to_sint16 x)
axiom is_to_uint32 (x : ℤ) : is_uint32 (to_uint32 x)
axiom is_to_sint32 (x : ℤ) : is_sint32 (to_sint32 x)
axiom is_to_uint64 (x : ℤ) : is_uint64 (to_uint64 x)
axiom is_to_sint64 (x : ℤ) : is_sint64 (to_sint64 x)
axiom id_uint (n : ℤ) (x : ℤ) : is_uint n x = (to_uint n x = x)
axiom id_sint (n : ℤ) (x : ℤ) : is_sint n x = (to_sint n x = x)
axiom id_uint8 (x : ℤ) (fact0 : is_uint8 x) : to_uint8 x = x
axiom id_sint8 (x : ℤ) (fact0 : is_sint8 x) : to_sint8 x = x
axiom id_uint16 (x : ℤ) (fact0 : is_uint16 x) : to_uint16 x = x
axiom id_sint16 (x : ℤ) (fact0 : is_sint16 x) : to_sint16 x = x
axiom id_uint32 (x : ℤ) (fact0 : is_uint32 x) : to_uint32 x = x
axiom id_sint32 (x : ℤ) (fact0 : is_sint32 x) : to_sint32 x = x
axiom id_uint64 (x : ℤ) (fact0 : is_uint64 x) : to_uint64 x = x
axiom id_sint64 (x : ℤ) (fact0 : is_sint64 x) : to_sint64 x = x
axiom proj_uint (n : ℤ) (x : ℤ) : to_uint n (to_uint n x) = to_uint n x
axiom proj_sint (n : ℤ) (x : ℤ) : to_sint n (to_sint n x) = to_sint n x
axiom proj_uint8 (x : ℤ) : to_uint8 (to_uint8 x) = to_uint8 x
axiom proj_sint8 (x : ℤ) : to_sint8 (to_sint8 x) = to_sint8 x
axiom proj_uint16 (x : ℤ) : to_uint16 (to_uint16 x) = to_uint16 x
axiom proj_sint16 (x : ℤ) : to_sint16 (to_sint16 x) = to_sint16 x
axiom proj_uint32 (x : ℤ) : to_uint32 (to_uint32 x) = to_uint32 x
axiom proj_sint32 (x : ℤ) : to_sint32 (to_sint32 x) = to_sint32 x
axiom proj_uint64 (x : ℤ) : to_uint64 (to_uint64 x) = to_uint64 x
axiom proj_sint64 (x : ℤ) : to_sint64 (to_sint64 x) = to_sint64 x
axiom proj_su (n : ℤ) (x : ℤ) : to_sint n (to_uint n x) = to_uint n x
axiom incl_su (n : ℤ) (x : ℤ) (fact0 : is_uint n x) : is_sint n x
axiom proj_su_uint (n : ℤ) (m : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ m) : to_sint (m + n) (to_uint n x) = to_uint n x
axiom proj_su_sint (n : ℤ) (m : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ m) : to_sint n (to_uint (m + (n + (1 : ℤ))) x) = to_sint n x
axiom proj_int8 (x : ℤ) : to_sint8 (to_uint8 x) = to_sint8 x
axiom proj_int16 (x : ℤ) : to_sint16 (to_uint16 x) = to_sint16 x
axiom proj_int32 (x : ℤ) : to_sint32 (to_uint32 x) = to_sint32 x
axiom proj_int64 (x : ℤ) : to_sint64 (to_uint64 x) = to_sint64 x
axiom proj_us_uint (n : ℤ) (m : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ m) : to_uint (n + (1 : ℤ)) (to_sint (m + n) x) = to_uint (n + (1 : ℤ)) x
axiom incl_uint (n : ℤ) (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ i) (fact2 : is_uint n x) : is_uint (n + i) x
axiom incl_sint (n : ℤ) (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ i) (fact2 : is_sint n x) : is_sint (n + i) x
axiom incl_int (n : ℤ) (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ i) (fact2 : is_uint n x) : is_sint (n + i) x
end Cint
namespace A_Strlen
noncomputable def p_valid_str (malloc_0 : ℤ -> ℤ) (mchar_0 : Memory.addr -> ℤ) (s : Memory.addr) := ∃(i : ℤ), mchar_0 (Memory.shift s i) = (0 : ℤ) ∧ Cint.is_uint64 i ∧ Memory.valid_rw malloc_0 (Memory.shift s (0 : ℤ)) ((1 : ℤ) + i) ∧ (∀(j : ℤ), j ≤ i → Cint.is_sint8 (mchar_0 (Memory.shift s j)))
axiom l_strlen : (Memory.addr -> ℤ) -> Memory.addr -> ℤ
axiom fix_l_strlen (mchar_0 : Memory.addr -> ℤ) (s : Memory.addr) : if mchar_0 (Memory.shift s (0 : ℤ)) = (0 : ℤ) then l_strlen mchar_0 s = (0 : ℤ) else Cint.to_uint64 ((1 : ℤ) + l_strlen mchar_0 (Memory.shift s (1 : ℤ))) = l_strlen mchar_0 s
axiom Q_TL_strlen (mchar_0 : Memory.addr -> ℤ) (s : Memory.addr) : Cint.is_uint64 (l_strlen mchar_0 s)
end A_Strlen
namespace A_Strnlen
noncomputable def p_valid_strn (malloc_0 : ℤ -> ℤ) (mchar_0 : Memory.addr -> ℤ) (s : Memory.addr) (cnt_0 : ℤ) := let a : Memory.addr := Memory.shift s (0 : ℤ); Memory.valid_rw malloc_0 a ((1 : ℤ) + cnt_0) ∨ (∃(i : ℤ), mchar_0 (Memory.shift s i) = (0 : ℤ) ∧ i < cnt_0 ∧ Cint.is_uint64 i ∧ Memory.valid_rw malloc_0 a ((1 : ℤ) + i)) ∧ (∀(j : ℤ), j ≤ cnt_0 → Cint.is_sint8 (mchar_0 (Memory.shift s j)))
axiom l_strnlen : (Memory.addr -> ℤ) -> Memory.addr -> ℤ -> ℤ
axiom fix_l_strnlen (mchar_0 : Memory.addr -> ℤ) (s : Memory.addr) (cnt_0 : ℤ) : if cnt_0 = (0 : ℤ) ∨ mchar_0 (Memory.shift s (0 : ℤ)) = (0 : ℤ) then l_strnlen mchar_0 s cnt_0 = (0 : ℤ) else Cint.to_uint64 ((1 : ℤ) + l_strnlen mchar_0 (Memory.shift s (1 : ℤ)) (Cint.to_uint64 (cnt_0 - (1 : ℤ)))) = l_strnlen mchar_0 s cnt_0
axiom Q_TL_strnlen (mchar_0 : Memory.addr -> ℤ) (s : Memory.addr) (cnt_0 : ℤ) : Cint.is_uint64 (l_strnlen mchar_0 s cnt_0)
end A_Strnlen
namespace A_StrnCmp
axiom l_strncmp_2' : (Memory.addr -> ℤ) -> Memory.addr -> Memory.addr -> ℤ -> ℤ
axiom fix_l_strncmp_2' (mchar_0 : Memory.addr -> ℤ) (s1_0 : Memory.addr) (s2_0 : Memory.addr) (n : ℤ) : if n = (0 : ℤ) then l_strncmp_2' mchar_0 s1_0 s2_0 n = (0 : ℤ) else if mchar_0 (Memory.shift s2_0 (0 : ℤ)) = mchar_0 (Memory.shift s1_0 (0 : ℤ)) then if mchar_0 (Memory.shift s1_0 (0 : ℤ)) = (0 : ℤ) then l_strncmp_2' mchar_0 s1_0 s2_0 n = (0 : ℤ) else l_strncmp_2' mchar_0 (Memory.shift s1_0 (1 : ℤ)) (Memory.shift s2_0 (1 : ℤ)) (Cint.to_uint64 (n - (1 : ℤ))) = l_strncmp_2' mchar_0 s1_0 s2_0 n else Cint.to_sint32 (mchar_0 (Memory.shift s1_0 (0 : ℤ)) - mchar_0 (Memory.shift s2_0 (0 : ℤ))) = l_strncmp_2' mchar_0 s1_0 s2_0 n
noncomputable def p_strnequal (mchar_0 : Memory.addr -> ℤ) (s1_0 : Memory.addr) (s2_0 : Memory.addr) (n : ℤ) := l_strncmp_2' mchar_0 s1_0 s2_0 n = (0 : ℤ)
axiom Q_TL_strncmp_2' (mchar_0 : Memory.addr -> ℤ) (s1_0 : Memory.addr) (s2_0 : Memory.addr) (n : ℤ) : Cint.is_sint32 (l_strncmp_2' mchar_0 s1_0 s2_0 n)
end A_StrnCmp
namespace A_SysfsStr
axiom l_sysfs_strlen : (Memory.addr -> ℤ) -> Memory.addr -> ℤ
axiom fix_l_sysfs_strlen (mchar_0 : Memory.addr -> ℤ) (s : Memory.addr) : if mchar_0 (Memory.shift s (0 : ℤ)) = (0 : ℤ) ∨ mchar_0 (Memory.shift s (0 : ℤ)) = (10 : ℤ) ∧ mchar_0 (Memory.shift s (1 : ℤ)) = (0 : ℤ) then l_sysfs_strlen mchar_0 s = (0 : ℤ) else Cint.to_uint64 ((1 : ℤ) + l_sysfs_strlen mchar_0 (Memory.shift s (1 : ℤ))) = l_sysfs_strlen mchar_0 s
axiom Q_TL_sysfs_strlen (mchar_0 : Memory.addr -> ℤ) (s : Memory.addr) : Cint.is_uint64 (l_sysfs_strlen mchar_0 s)
end A_SysfsStr
namespace sysfs_streq_Why3_ide_VCsysfs_streq_assert_13_goal19
theorem goal19 (a : Memory.addr) (i : ℤ) (a_1 : Memory.addr) (t_1 : Memory.addr -> ℤ) (t : ℤ -> ℤ) : let a_2 : Memory.addr := Memory.shift a i; let a_3 : Memory.addr := Memory.shift a_1 i; let x : ℤ := A_SysfsStr.l_sysfs_strlen t_1 a_3; t_1 a_2 = (0 : ℤ) → t_1 a_3 = (10 : ℤ) → x = A_SysfsStr.l_sysfs_strlen t_1 a_2 → t_1 (Memory.shift a_1 ((1 : ℤ) + i)) = (0 : ℤ) → i ≤ A_Strlen.l_strlen t_1 a → i ≤ A_Strlen.l_strlen t_1 a_1 → Memory.region (Memory.addr.base a) ≤ (0 : ℤ) → Memory.region (Memory.addr.base a_1) ≤ (0 : ℤ) → Memory.linked t → Memory.sconst t_1 → Cint.is_uint64 i → A_Strlen.p_valid_str t t_1 a → A_Strlen.p_valid_str t t_1 a_1 → A_StrnCmp.p_strnequal t_1 a_1 a i → A_Strlen.p_valid_str t t_1 a_2 → A_Strlen.p_valid_str t t_1 a_3 → A_StrnCmp.p_strnequal t_1 a_3 a_2 x → (∀(i_1 : ℤ), (0 : ℤ) ≤ i_1 → i_1 < i → t_1 (Memory.shift a_1 i_1) = t_1 (Memory.shift a i_1)) → (∀(i_1 : ℤ), let x_1 : ℤ := t_1 (Memory.shift a i_1); let x_2 : ℤ := t_1 (Memory.shift a_1 i_1); (0 : ℤ) ≤ i_1 → i_1 < i → ¬x_1 = (0 : ℤ) ∧ ¬x_2 = (0 : ℤ) ∧ x_2 = x_1) → A_SysfsStr.l_sysfs_strlen t_1 a_1 = i
  := sorry
end sysfs_streq_Why3_ide_VCsysfs_streq_assert_13_goal19
