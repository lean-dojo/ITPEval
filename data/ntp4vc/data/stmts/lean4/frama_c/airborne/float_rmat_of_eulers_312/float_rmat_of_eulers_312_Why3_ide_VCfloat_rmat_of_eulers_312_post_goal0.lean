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
namespace Cmath
axiom abs_def (x : ℤ) : if (0 : ℤ) ≤ x then abs x = x else abs x = -x
end Cmath
namespace Square
axiom sqrt_lin1 (x : ℝ) (fact0 : (1 : ℝ) < x) : Real.sqrt x < x
axiom sqrt_lin0 (x : ℝ) (fact0 : (0 : ℝ) < x) (fact1 : x < (1 : ℝ)) : x < Real.sqrt x
axiom sqrt_0 : Real.sqrt (0 : ℝ) = (0 : ℝ)
axiom sqrt_1 : Real.sqrt (1 : ℝ) = (1 : ℝ)
end Square
namespace Compound
end Compound
namespace Cfloat
noncomputable def is_float32 (x : ℝ) := True
noncomputable def is_float64 (x : ℝ) := True
inductive rounding_mode where
  | Up : rounding_mode
  | Down : rounding_mode
  | ToZero : rounding_mode
  | NearestTiesToAway : rounding_mode
  | NearestTiesToEven : rounding_mode
axiom inhabited_axiom_rounding_mode : Inhabited rounding_mode
attribute [instance] inhabited_axiom_rounding_mode
axiom round_double : rounding_mode -> ℝ -> ℝ
axiom round_float : rounding_mode -> ℝ -> ℝ
axiom float_32 (x : ℝ) : x = round_float rounding_mode.NearestTiesToEven x
axiom float_64 (x : ℝ) : x = round_double rounding_mode.NearestTiesToEven x
inductive float_kind where
  | Real : float_kind
  | Float32 : float_kind
  | Float64 : float_kind
  | NaN : float_kind
  | Inf_pos : float_kind
  | Inf_neg : float_kind
axiom inhabited_axiom_float_kind : Inhabited float_kind
attribute [instance] inhabited_axiom_float_kind
axiom classify_float : ℝ -> float_kind
noncomputable def is_finite32 (x : ℝ) := classify_float x = float_kind.Float32
noncomputable def is_finite64 (x : ℝ) := classify_float x = float_kind.Float32 ∨ classify_float x = float_kind.Float64
noncomputable def is_NaN (x : ℝ) := classify_float x = float_kind.NaN
noncomputable def is_infinite (x : ℝ) := classify_float x = float_kind.Inf_pos ∨ classify_float x = float_kind.Inf_neg
noncomputable def is_positive_infinite (x : ℝ) := classify_float x = float_kind.Inf_pos
noncomputable def is_negative_infinite (x : ℝ) := classify_float x = float_kind.Inf_neg
axiom is_finite_to_float_32 (x : ℝ) : is_finite32 x
axiom is_finite_to_float_64 (x : ℝ) : is_finite64 x
axiom model : ℝ -> ℝ
noncomputable def delta (x : ℝ) := abs (x - model x)
noncomputable def error (x : ℝ) := delta x / abs (model x)
axiom model_float_32 : True
axiom model_float_64 : True
axiom model_add (x : ℝ) (y : ℝ) : model (x + y) = model x + model y
axiom model_mul (x : ℝ) (y : ℝ) : model (x * y) = model x * model y
axiom model_div (x : ℝ) (y : ℝ) : model (x / y) = model x / model y
axiom model_sqrt (x : ℝ) : model (Real.sqrt x) = Real.sqrt (model x)
end Cfloat
namespace Axiomatic15
noncomputable def p_finite_floateulers (mflt_0 : Memory.addr -> ℝ) (e : Memory.addr) := Cfloat.is_finite32 (mflt_0 (Memory.shift e (0 : ℤ))) ∧ Cfloat.is_finite32 (mflt_0 (Memory.shift e (2 : ℤ))) ∧ Cfloat.is_finite32 (mflt_0 (Memory.shift e (1 : ℤ)))
noncomputable def p_rvalid_floateulers (malloc_0 : ℤ -> ℤ) (mflt_0 : Memory.addr -> ℝ) (e : Memory.addr) := p_finite_floateulers mflt_0 e ∧ Memory.valid_rd malloc_0 e (3 : ℤ)
end Axiomatic15
namespace S10_RealRMat_s
structure s10_realrmat_s where
  f10_realrmat_s_a00 : ℝ
  f10_realrmat_s_a01 : ℝ
  f10_realrmat_s_a02 : ℝ
  f10_realrmat_s_a10 : ℝ
  f10_realrmat_s_a11 : ℝ
  f10_realrmat_s_a12 : ℝ
  f10_realrmat_s_a20 : ℝ
  f10_realrmat_s_a21 : ℝ
  f10_realrmat_s_a22 : ℝ
axiom inhabited_axiom_s10_realrmat_s : Inhabited s10_realrmat_s
attribute [instance] inhabited_axiom_s10_realrmat_s
noncomputable def eqs10_realrmat_s (s : s10_realrmat_s) (s_1 : s10_realrmat_s) := s10_realrmat_s.f10_realrmat_s_a00 s_1 = s10_realrmat_s.f10_realrmat_s_a00 s ∧ s10_realrmat_s.f10_realrmat_s_a01 s_1 = s10_realrmat_s.f10_realrmat_s_a01 s ∧ s10_realrmat_s.f10_realrmat_s_a02 s_1 = s10_realrmat_s.f10_realrmat_s_a02 s ∧ s10_realrmat_s.f10_realrmat_s_a10 s_1 = s10_realrmat_s.f10_realrmat_s_a10 s ∧ s10_realrmat_s.f10_realrmat_s_a11 s_1 = s10_realrmat_s.f10_realrmat_s_a11 s ∧ s10_realrmat_s.f10_realrmat_s_a12 s_1 = s10_realrmat_s.f10_realrmat_s_a12 s ∧ s10_realrmat_s.f10_realrmat_s_a20 s_1 = s10_realrmat_s.f10_realrmat_s_a20 s ∧ s10_realrmat_s.f10_realrmat_s_a21 s_1 = s10_realrmat_s.f10_realrmat_s_a21 s ∧ s10_realrmat_s.f10_realrmat_s_a22 s_1 = s10_realrmat_s.f10_realrmat_s_a22 s
end S10_RealRMat_s
namespace Axiomatic17
noncomputable def l_l_rmat_of_floatrmat (mflt_0 : Memory.addr -> ℝ) (rmat_0 : Memory.addr) := let a : Memory.addr := Memory.shift rmat_0 (0 : ℤ); S10_RealRMat_s.s10_realrmat_s.mk (mflt_0 (Memory.shift a (0 : ℤ))) (mflt_0 (Memory.shift a (1 : ℤ))) (mflt_0 (Memory.shift a (2 : ℤ))) (mflt_0 (Memory.shift a (3 : ℤ))) (mflt_0 (Memory.shift a (4 : ℤ))) (mflt_0 (Memory.shift a (5 : ℤ))) (mflt_0 (Memory.shift a (6 : ℤ))) (mflt_0 (Memory.shift a (7 : ℤ))) (mflt_0 (Memory.shift a (8 : ℤ)))
noncomputable def l_determinant (rmat_0 : S10_RealRMat_s.s10_realrmat_s) := let r : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a00 rmat_0; let r_1 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a12 rmat_0; let r_2 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a21 rmat_0; let r_3 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a01 rmat_0; let r_4 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a10 rmat_0; let r_5 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a22 rmat_0; let r_6 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a02 rmat_0; let r_7 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a11 rmat_0; let r_8 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a20 rmat_0; r * r_7 * r_5 + r_3 * r_1 * r_8 + r_6 * r_4 * r_2 - r * r_1 * r_2 - r_3 * r_4 * r_5 - r_6 * r_7 * r_8
noncomputable def p_special_orthogonal (rmat_0 : S10_RealRMat_s.s10_realrmat_s) := l_determinant rmat_0 = (1 : ℝ)
noncomputable def l_transpose (rmat_0 : S10_RealRMat_s.s10_realrmat_s) := S10_RealRMat_s.s10_realrmat_s.mk (S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a00 rmat_0) (S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a10 rmat_0) (S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a20 rmat_0) (S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a01 rmat_0) (S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a11 rmat_0) (S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a21 rmat_0) (S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a02 rmat_0) (S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a12 rmat_0) (S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a22 rmat_0)
noncomputable def l_mult_realrmat (rmat1_0 : S10_RealRMat_s.s10_realrmat_s) (rmat2_0 : S10_RealRMat_s.s10_realrmat_s) := let r : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a00 rmat1_0; let r_1 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a00 rmat2_0; let r_2 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a01 rmat1_0; let r_3 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a10 rmat2_0; let r_4 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a02 rmat1_0; let r_5 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a20 rmat2_0; let r_6 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a01 rmat2_0; let r_7 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a11 rmat2_0; let r_8 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a21 rmat2_0; let r_9 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a02 rmat2_0; let r_10 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a12 rmat2_0; let r_11 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a22 rmat2_0; let r_12 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a10 rmat1_0; let r_13 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a11 rmat1_0; let r_14 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a12 rmat1_0; let r_15 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a20 rmat1_0; let r_16 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a21 rmat1_0; let r_17 : ℝ := S10_RealRMat_s.s10_realrmat_s.f10_realrmat_s_a22 rmat1_0; S10_RealRMat_s.s10_realrmat_s.mk (r * r_1 + r_2 * r_3 + r_4 * r_5) (r * r_6 + r_2 * r_7 + r_4 * r_8) (r * r_9 + r_2 * r_10 + r_4 * r_11) (r_12 * r_1 + r_13 * r_3 + r_14 * r_5) (r_12 * r_6 + r_13 * r_7 + r_14 * r_8) (r_12 * r_9 + r_13 * r_10 + r_14 * r_11) (r_15 * r_1 + r_16 * r_3 + r_17 * r_5) (r_15 * r_6 + r_16 * r_7 + r_17 * r_8) (r_15 * r_9 + r_16 * r_10 + r_17 * r_11)
noncomputable def p_rotation_matrix (rmat_0 : S10_RealRMat_s.s10_realrmat_s) := S10_RealRMat_s.eqs10_realrmat_s (l_mult_realrmat rmat_0 (l_transpose rmat_0)) (S10_RealRMat_s.s10_realrmat_s.mk (1 : ℝ) (0 : ℝ) (0 : ℝ) (0 : ℝ) (1 : ℝ) (0 : ℝ) (0 : ℝ) (0 : ℝ) (1 : ℝ))
end Axiomatic17
namespace float_rmat_of_eulers_312_Why3_ide_VCfloat_rmat_of_eulers_312_post_goal0
theorem goal0 (t_1 : Memory.addr -> ℝ) (a_1 : Memory.addr) (a : Memory.addr) (t : ℤ -> ℤ) : let r : ℝ := t_1 (Memory.shift a_1 (0 : ℤ)); let r_1 : ℝ := Real.sin r; let r_2 : ℝ := t_1 (Memory.shift a_1 (2 : ℤ)); let r_3 : ℝ := Real.sin r_2; let r_4 : ℝ := t_1 (Memory.shift a_1 (1 : ℤ)); let r_5 : ℝ := Real.sin r_4; let r_6 : ℝ := Real.cos r; let r_7 : ℝ := Real.cos r_2; let r_8 : ℝ := Real.cos r_4; let a_2 : Memory.addr := Memory.shift a (0 : ℤ); let r_9 : ℝ := r_1 * r_5; let r_10 : ℝ := -r_6; let r_11 : ℝ := r_1 * r_8; Memory.region (Memory.addr.base a) ≤ (0 : ℤ) → Memory.region (Memory.addr.base a_1) ≤ (0 : ℤ) → r_1 ≤ (1 : ℝ) → r_3 ≤ (1 : ℝ) → r_5 ≤ (1 : ℝ) → r_6 ≤ (1 : ℝ) → r_7 ≤ (1 : ℝ) → r_8 ≤ (1 : ℝ) → -(1 : ℝ) ≤ r_1 → -(1 : ℝ) ≤ r_3 → -(1 : ℝ) ≤ r_5 → -(1 : ℝ) ≤ r_6 → -(1 : ℝ) ≤ r_7 → -(1 : ℝ) ≤ r_8 → Memory.linked t → Memory.valid_rw t a (9 : ℤ) → Axiomatic15.p_rvalid_floateulers t t_1 a_1 → Cfloat.is_finite32 r → Cfloat.is_finite32 r_2 → Cfloat.is_finite32 r_4 → Cfloat.is_float32 r → Cfloat.is_float32 r_2 → Cfloat.is_float32 r_4 → Cfloat.is_finite32 r_1 → Cfloat.is_finite32 r_3 → Cfloat.is_finite32 r_5 → Cfloat.is_finite32 r_6 → Cfloat.is_finite32 r_7 → Cfloat.is_finite32 r_8 → Cfloat.is_float32 r_1 → Cfloat.is_float32 r_3 → Cfloat.is_float32 r_5 → Cfloat.is_float32 r_6 → Cfloat.is_float32 r_7 → Cfloat.is_float32 r_8 → Axiomatic17.p_rotation_matrix (Axiomatic17.l_l_rmat_of_floatrmat (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update t_1 (Memory.shift a_2 (0 : ℤ)) (r_8 * r_7 + -(r_9 * r_3))) (Memory.shift a_2 (1 : ℤ)) (r_8 * r_3 + r_9 * r_7)) (Memory.shift a_2 (2 : ℤ)) (r_10 * r_5)) (Memory.shift a_2 (3 : ℤ)) (r_10 * r_3)) (Memory.shift a_2 (4 : ℤ)) (r_6 * r_7)) (Memory.shift a_2 (5 : ℤ)) r_1) (Memory.shift a_2 (6 : ℤ)) (r_5 * r_7 + r_11 * r_3)) (Memory.shift a_2 (7 : ℤ)) (r_5 * r_3 + -(r_11 * r_7))) (Memory.shift a_2 (8 : ℤ)) (r_6 * r_8)) a)
  := sorry
end float_rmat_of_eulers_312_Why3_ide_VCfloat_rmat_of_eulers_312_post_goal0
