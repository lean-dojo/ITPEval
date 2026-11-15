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
namespace A_thread_variables_properties
axiom l_size : ℤ
axiom Q_some : (0 : ℤ) < l_size ∧ l_size ≤ (2147483647 : ℤ)
end A_thread_variables_properties
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
namespace A_schedule_cpumask
axiom l_idle_cpu : ℤ -> ℤ
axiom l_sched_group_cpus : Memory.addr -> Memory.addr
axiom l_sched_group_mask : Memory.addr -> Memory.addr
axiom l_group_balance_mask : Memory.addr -> Memory.addr
axiom l_group_balance_cpu : Memory.addr -> ℤ
axiom l_cpu_smt_mask : ℤ -> Memory.addr
noncomputable def p_idle_core (mptr_0 : Memory.addr -> Memory.addr) (mint_0 : Memory.addr -> ℤ) (cpu_0 : ℤ) := ∀(i : ℤ), ¬mint_0 (Memory.shift (mptr_0 (Memory.shift (l_cpu_smt_mask cpu_0) (0 : ℤ))) i) = (0 : ℤ) → (0 : ℤ) ≤ i → i < A_thread_variables_properties.l_size → ¬l_idle_cpu i = (0 : ℤ)
axiom Q_TL_idle_cpu (cpu_0 : ℤ) : Cint.is_uint8 (l_idle_cpu cpu_0)
axiom Q_mask_refl (i : ℤ) (mint_0 : Memory.addr -> ℤ) (mptr_0 : Memory.addr -> Memory.addr) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < A_thread_variables_properties.l_size) : ¬mint_0 (Memory.shift (mptr_0 (Memory.shift (l_cpu_smt_mask i) (0 : ℤ))) i) = (0 : ℤ)
axiom Q_mask_symm (mint_0 : Memory.addr -> ℤ) (mptr_0 : Memory.addr -> Memory.addr) (j : ℤ) (i : ℤ) (fact0 : ¬mint_0 (Memory.shift (mptr_0 (Memory.shift (l_cpu_smt_mask j) (0 : ℤ))) i) = (0 : ℤ)) (fact1 : (0 : ℤ) ≤ i) (fact2 : i < A_thread_variables_properties.l_size) (fact3 : (0 : ℤ) ≤ j) (fact4 : j < A_thread_variables_properties.l_size) : ¬mint_0 (Memory.shift (mptr_0 (Memory.shift (l_cpu_smt_mask i) (0 : ℤ))) j) = (0 : ℤ)
axiom Q_mask_trans (mptr_0 : Memory.addr -> Memory.addr) (i : ℤ) (mint_0 : Memory.addr -> ℤ) (j : ℤ) (k : ℤ) : ¬mint_0 (Memory.shift (mptr_0 (Memory.shift (l_cpu_smt_mask i) (0 : ℤ))) j) = (0 : ℤ) → ¬mint_0 (Memory.shift (mptr_0 (Memory.shift (l_cpu_smt_mask j) (0 : ℤ))) k) = (0 : ℤ) → (0 : ℤ) ≤ i → i < A_thread_variables_properties.l_size → (0 : ℤ) ≤ j → j < A_thread_variables_properties.l_size → (0 : ℤ) ≤ k → k < A_thread_variables_properties.l_size → ¬mint_0 (Memory.shift (mptr_0 (Memory.shift (l_cpu_smt_mask i) (0 : ℤ))) k) = (0 : ℤ)
end A_schedule_cpumask
namespace Cbits
axiom bit_testb : ℤ -> ℤ -> Bool
axiom bit_test : ℤ -> ℤ -> Prop
axiom lnot : ℤ -> ℤ
axiom land : ℤ -> ℤ -> ℤ
axiom lxor : ℤ -> ℤ -> ℤ
axiom lor : ℤ -> ℤ -> ℤ
axiom lsl : ℤ -> ℤ -> ℤ
axiom lsr : ℤ -> ℤ -> ℤ
axiom lnot_bool : lnot (0 : ℤ) = -(1 : ℤ) ∧ lnot (-(1 : ℤ)) = (0 : ℤ)
axiom land_idemp (x : ℤ) : land x x = x
axiom land_idemp_bis (x : ℤ) (y : ℤ) : land x (land x y) = land x y
axiom land_0 (x : ℤ) : land (0 : ℤ) x = (0 : ℤ)
axiom land_0bis (x : ℤ) : land x (0 : ℤ) = (0 : ℤ)
axiom land_1 (x : ℤ) : land (-(1 : ℤ)) x = x
axiom land_1bis (x : ℤ) : land x (-(1 : ℤ)) = x
axiom land_bool : land (0 : ℤ) (0 : ℤ) = (0 : ℤ) ∧ land (0 : ℤ) (1 : ℤ) = (0 : ℤ) ∧ land (1 : ℤ) (0 : ℤ) = (0 : ℤ) ∧ land (1 : ℤ) (1 : ℤ) = (1 : ℤ)
axiom lor_idemp (x : ℤ) : lor x x = x
axiom lor_idemp_bis (x : ℤ) (y : ℤ) : lor x (lor x y) = lor x y
axiom lor_1 (x : ℤ) : lor (-(1 : ℤ)) x = -(1 : ℤ)
axiom lor_1bis (x : ℤ) : lor x (-(1 : ℤ)) = -(1 : ℤ)
axiom lor_0 (x : ℤ) : lor (0 : ℤ) x = x
axiom lor_0bis (x : ℤ) : lor x (0 : ℤ) = x
axiom lor_bool : lor (0 : ℤ) (0 : ℤ) = (0 : ℤ) ∧ lor (0 : ℤ) (1 : ℤ) = (1 : ℤ) ∧ lor (1 : ℤ) (0 : ℤ) = (1 : ℤ) ∧ lor (1 : ℤ) (1 : ℤ) = (1 : ℤ)
axiom lxor_nilpotent (x : ℤ) : lxor x x = (0 : ℤ)
axiom lxor_nilpotent_bis (x : ℤ) (y : ℤ) : lxor x (lxor x y) = y
axiom lxor_1 (x : ℤ) : lxor (-(1 : ℤ)) x = lnot x
axiom lxor_1bis (x : ℤ) : lxor x (-(1 : ℤ)) = lnot x
axiom lxor_0 (x : ℤ) : lxor (0 : ℤ) x = x
axiom lxor_0bis (x : ℤ) : lxor x (0 : ℤ) = x
axiom lxor_bool : lxor (0 : ℤ) (0 : ℤ) = (0 : ℤ) ∧ lxor (0 : ℤ) (1 : ℤ) = (1 : ℤ) ∧ lxor (1 : ℤ) (0 : ℤ) = (1 : ℤ) ∧ lxor (1 : ℤ) (1 : ℤ) = (0 : ℤ)
axiom lsl_0 (x : ℤ) : lsl x (0 : ℤ) = x
axiom lsl_1 (x : ℤ) : lsl x (1 : ℤ) = (2 : ℤ) * x
axiom lsl_add (p : ℤ) (q : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ p) (fact1 : (0 : ℤ) ≤ q) : lsl (lsl x p) q = lsl x (p + q)
axiom lsr_0 (x : ℤ) : lsr x (0 : ℤ) = x
axiom lsr_1 (x : ℤ) (fact0 : (0 : ℤ) ≤ x) : lsr x (1 : ℤ) = Int.tdiv x (2 : ℤ)
axiom lsr_add (p : ℤ) (q : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ p) (fact1 : (0 : ℤ) ≤ q) : lsr (lsr x p) q = lsr x (p + q)
axiom lsl_lsr_add (q : ℤ) (p : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ q) (fact1 : q ≤ p) : lsr (lsl x p) q = lsl x (p - q)
axiom bit_test_def (x : ℤ) (k : ℤ) : (bit_testb x k = true) = bit_test x k
axiom bit_test_extraction (k : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ k) : (¬land x (lsl (1 : ℤ) k) = (0 : ℤ)) = bit_test x k
axiom bit_test_extraction_eq (k : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ k) : (land x (lsl (1 : ℤ) k) = lsl (1 : ℤ) k) = bit_test x k
axiom lsl_1_0 : lsl (1 : ℤ) (0 : ℤ) = (1 : ℤ)
axiom bit_test_extraction_bis (x : ℤ) (fact0 : ¬land (1 : ℤ) x = (0 : ℤ)) : bit_test x (0 : ℤ)
axiom bit_test_extraction_bis_eq (x : ℤ) (fact0 : bit_test x (0 : ℤ)) : land (1 : ℤ) x = (1 : ℤ)
axiom lnot_extraction_bool (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) : bit_testb (lnot x) i = (¬bit_testb x i)
axiom lnot_extraction (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) : bit_test (lnot x) i = (¬bit_test x i)
axiom land_extraction_bool (i : ℤ) (x : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ i) : bit_testb (land x y) i = (bit_testb x i && bit_testb y i)
axiom land_extraction (i : ℤ) (x : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ i) : bit_test (land x y) i = (bit_test x i ∧ bit_test y i)
axiom lor_extraction_bool (i : ℤ) (x : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ i) : bit_testb (lor x y) i = (bit_testb x i || bit_testb y i)
axiom lor_extraction (i : ℤ) (x : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ i) : bit_test (lor x y) i = (bit_test x i ∨ bit_test y i)
axiom lxor_extraction_bool (i : ℤ) (x : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ i) : bit_testb (lxor x y) i = (bit_testb x i ^^ bit_testb y i)
axiom lxor_extraction (i : ℤ) (x : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ i) : bit_test (lxor x y) i = (bit_test x i = (¬bit_test y i))
axiom lsl_1_two_power (n : ℤ) (fact0 : (0 : ℤ) ≤ n) : lsl (1 : ℤ) n = Cint.two_power_abs n
axiom land_1_lsl_1 (n : ℤ) (a : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : a < lsl (1 : ℤ) n) : (2 : ℤ) * a + land (1 : ℤ) x < lsl (1 : ℤ) ((1 : ℤ) + n)
axiom lsl_extraction_sup_bool (n : ℤ) (m : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ m) (fact2 : n ≤ m) : bit_testb (lsl x n) m = bit_testb x (m - n)
axiom lsl_extraction_sup (n : ℤ) (m : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ m) (fact2 : n ≤ m) : bit_test (lsl x n) m = bit_test x (m - n)
axiom lsl_extraction_inf_bool (n : ℤ) (m : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ m) (fact2 : m < n) : bit_testb (lsl x n) m = false
axiom lsl_extraction_inf (n : ℤ) (m : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ m) (fact2 : m < n) : ¬bit_test (lsl x n) m
axiom lsr_extraction_bool (n : ℤ) (m : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ m) : bit_testb (lsr x n) m = bit_testb x (m + n)
axiom lsr_extractionl (n : ℤ) (m : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : (0 : ℤ) ≤ m) : bit_test (lsr x n) m = bit_test x (m + n)
axiom lsl1_extraction_bool (i : ℤ) (j : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : (0 : ℤ) ≤ j) : bit_testb (lsl (1 : ℤ) i) j = (if i = j then true else false)
axiom lsl1_extraction (i : ℤ) (j : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : (0 : ℤ) ≤ j) : bit_test (lsl (1 : ℤ) i) j = (i = j)
axiom pos_extraction_sup (x : ℤ) (i : ℤ) (j : ℤ) (fact0 : (0 : ℤ) ≤ x) (fact1 : (0 : ℤ) ≤ i) (fact2 : x < lsl (1 : ℤ) i) (fact3 : i ≤ j) : ¬bit_test x j
axiom pos_extraction_sup_inv (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : ∀(j : ℤ), i ≤ j → ¬bit_test x j) : (0 : ℤ) ≤ x ∧ x < lsl (1 : ℤ) i
axiom to_uint_extraction_sup (n : ℤ) (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : n ≤ i) (fact2 : Cint.is_uint n x) : ¬bit_test x i
axiom to_uint_extraction_inf_bool (i : ℤ) (n : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < n) : bit_testb (Cint.to_uint n x) i = bit_testb x i
axiom to_uint_extraction_inf (i : ℤ) (n : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < n) : bit_test (Cint.to_uint n x) i = bit_test x i
axiom is_uint_ext (n : ℤ) (x : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : Cint.is_uint n x) (fact2 : Cint.is_uint n y) (fact3 : ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → bit_test x i = bit_test y i) : x = y
axiom to_uint8_extraction_sup (i : ℤ) (x : ℤ) (fact0 : (8 : ℤ) ≤ i) (fact1 : Cint.is_uint8 x) : ¬bit_test x i
axiom to_uint8_extraction_inf_bool (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (8 : ℤ)) : bit_testb (Cint.to_uint8 x) i = bit_testb x i
axiom to_uint8_extraction_inf (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (8 : ℤ)) : bit_test (Cint.to_uint8 x) i = bit_test x i
axiom is_uint8_ext (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint8 x) (fact1 : Cint.is_uint8 y) (fact2 : ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (8 : ℤ) → bit_test x i = bit_test y i) : x = y
axiom to_uint16_extraction_sup (i : ℤ) (x : ℤ) (fact0 : (16 : ℤ) ≤ i) (fact1 : Cint.is_uint16 x) : ¬bit_test x i
axiom to_uint16_extraction_inf_bool (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (16 : ℤ)) : bit_testb (Cint.to_uint16 x) i = bit_testb x i
axiom to_uint16_extraction_inf (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (16 : ℤ)) : bit_test (Cint.to_uint16 x) i = bit_test x i
axiom is_uint16_ext (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint16 x) (fact1 : Cint.is_uint16 y) (fact2 : ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (16 : ℤ) → bit_test x i = bit_test y i) : x = y
axiom to_uint32_extraction_sup (i : ℤ) (x : ℤ) (fact0 : (32 : ℤ) ≤ i) (fact1 : Cint.is_uint32 x) : ¬bit_test x i
axiom to_uint32_extraction_inf_bool (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (32 : ℤ)) : bit_testb (Cint.to_uint32 x) i = bit_testb x i
axiom to_uint32_extraction_inf (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (32 : ℤ)) : bit_test (Cint.to_uint32 x) i = bit_test x i
axiom is_uint32_ext (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint32 x) (fact1 : Cint.is_uint32 y) (fact2 : ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (32 : ℤ) → bit_test x i = bit_test y i) : x = y
axiom to_uint64_extraction_sup (i : ℤ) (x : ℤ) (fact0 : (64 : ℤ) ≤ i) (fact1 : Cint.is_uint64 x) : ¬bit_test x i
axiom to_uint64_extraction_inf_bool (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (64 : ℤ)) : bit_testb (Cint.to_uint64 x) i = bit_testb x i
axiom to_uint64_extraction_inf (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (64 : ℤ)) : bit_test (Cint.to_uint64 x) i = bit_test x i
axiom is_uint64_ext (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint64 x) (fact1 : Cint.is_uint64 y) (fact2 : ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < (64 : ℤ) → bit_test x i = bit_test y i) : x = y
axiom to_sint_extraction_sup (n : ℤ) (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : n ≤ i) (fact2 : Cint.is_sint n x) : bit_test x i = (x < (0 : ℤ))
axiom to_sint_extraction_inf_bool (i : ℤ) (n : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < n) : bit_testb (Cint.to_sint n x) i = bit_testb x i
axiom to_sint_extraction_inf (i : ℤ) (n : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < n) : bit_test (Cint.to_sint n x) i = bit_test x i
axiom is_sint_ext (n : ℤ) (x : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : Cint.is_sint n x) (fact2 : Cint.is_sint n y) (fact3 : ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i ≤ n → bit_test x i = bit_test y i) : x = y
axiom to_sint8_extraction_sup (i : ℤ) (x : ℤ) (fact0 : (7 : ℤ) ≤ i) (fact1 : Cint.is_sint8 x) : bit_test x i = (x < (0 : ℤ))
axiom to_sint8_extraction_inf_bool (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (7 : ℤ)) : bit_testb (Cint.to_sint8 x) i = bit_testb x i
axiom to_sint8_extraction_inf (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (7 : ℤ)) : bit_test (Cint.to_sint8 x) i = bit_test x i
axiom is_sint8_ext (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint8 x) (fact1 : Cint.is_sint8 y) (fact2 : ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i ≤ (7 : ℤ) → bit_test x i = bit_test y i) : x = y
axiom to_sint16_extraction_sup (i : ℤ) (x : ℤ) (fact0 : (15 : ℤ) ≤ i) (fact1 : Cint.is_sint16 x) : bit_test x i = (x < (0 : ℤ))
axiom to_sint16_extraction_inf_bool (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (15 : ℤ)) : bit_testb (Cint.to_sint16 x) i = bit_testb x i
axiom to_sint16_extraction_inf (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (15 : ℤ)) : bit_test (Cint.to_sint16 x) i = bit_test x i
axiom is_sint16_ext (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint16 x) (fact1 : Cint.is_sint16 y) (fact2 : ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i ≤ (15 : ℤ) → bit_test x i = bit_test y i) : x = y
axiom to_sint32_extraction_sup (i : ℤ) (x : ℤ) (fact0 : (31 : ℤ) ≤ i) (fact1 : Cint.is_sint32 x) : bit_test x i = (x < (0 : ℤ))
axiom to_sint32_extraction_inf_bool (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (31 : ℤ)) : bit_testb (Cint.to_sint32 x) i = bit_testb x i
axiom to_sint32_extraction_inf (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (31 : ℤ)) : bit_test (Cint.to_sint32 x) i = bit_test x i
axiom is_sint32_ext (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint32 x) (fact1 : Cint.is_sint32 y) (fact2 : ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i ≤ (31 : ℤ) → bit_test x i = bit_test y i) : x = y
axiom to_sint64_extraction_sup (i : ℤ) (x : ℤ) (fact0 : (63 : ℤ) ≤ i) (fact1 : Cint.is_sint64 x) : bit_test x i = (x < (0 : ℤ))
axiom to_sint64_extraction_inf_bool (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (63 : ℤ)) : bit_testb (Cint.to_sint64 x) i = bit_testb x i
axiom to_sint64_extraction_inf (i : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < (63 : ℤ)) : bit_test (Cint.to_sint64 x) i = bit_test x i
axiom is_sint64_ext (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint64 x) (fact1 : Cint.is_sint64 y) (fact2 : ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i ≤ (63 : ℤ) → bit_test x i = bit_test y i) : x = y
axiom to_uint_lor (n : ℤ) (x : ℤ) (y : ℤ) : Cint.to_uint n (lor x y) = lor (Cint.to_uint n x) (Cint.to_uint n y)
axiom to_uint8_lor (x : ℤ) (y : ℤ) : Cint.to_uint8 (lor x y) = lor (Cint.to_uint8 x) (Cint.to_uint (8 : ℤ) y)
axiom to_uint16_lor (x : ℤ) (y : ℤ) : Cint.to_uint16 (lor x y) = lor (Cint.to_uint16 x) (Cint.to_uint16 y)
axiom to_uint32_lor (x : ℤ) (y : ℤ) : Cint.to_uint32 (lor x y) = lor (Cint.to_uint32 x) (Cint.to_uint32 y)
axiom to_uint64_lor (x : ℤ) (y : ℤ) : Cint.to_uint64 (lor x y) = lor (Cint.to_uint64 x) (Cint.to_uint64 y)
axiom is_uint_lxor (n : ℤ) (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint n x) (fact1 : Cint.is_uint n y) : Cint.to_uint n (lxor x y) = lxor x y
axiom is_uint_lor (n : ℤ) (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint n x) (fact1 : Cint.is_uint n y) : Cint.to_uint n (lor x y) = lor x y
axiom is_uint_land (n : ℤ) (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint n x) (fact1 : Cint.is_uint n y) : Cint.to_uint n (land x y) = land x y
axiom is_uint_lsr (y : ℤ) (n : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : Cint.is_uint n x) : Cint.to_uint n (lsr x y) = lsr x y
axiom is_uint_lsl1_inf (y : ℤ) (n : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : y < n) : Cint.to_uint n (lsl (1 : ℤ) y) = lsl (1 : ℤ) y
axiom is_uint_lsl1_sup (n : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : n ≤ y) : Cint.to_uint n (lsl (1 : ℤ) y) = (0 : ℤ)
axiom is_uint8_lxor (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint8 x) (fact1 : Cint.is_uint8 y) : Cint.to_uint8 (lxor x y) = lxor x y
axiom is_uint8_lor (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint8 x) (fact1 : Cint.is_uint8 y) : Cint.to_uint8 (lor x y) = lor x y
axiom is_uint8_land (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint8 x) (fact1 : Cint.is_uint8 y) : Cint.to_uint8 (land x y) = land x y
axiom is_uint8_lsr (y : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : Cint.is_uint8 x) : Cint.to_uint8 (lsr x y) = lsr x y
axiom is_uint8_lsl1_inf (y : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : y < (8 : ℤ)) : Cint.to_uint8 (lsl (1 : ℤ) y) = lsl (1 : ℤ) y
axiom is_uint8_lsl1_sup (y : ℤ) (fact0 : (8 : ℤ) ≤ y) : Cint.to_uint8 (lsl (1 : ℤ) y) = (0 : ℤ)
axiom is_uint16_lxor (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint16 x) (fact1 : Cint.is_uint16 y) : Cint.to_uint16 (lxor x y) = lxor x y
axiom is_uint16_lor (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint16 x) (fact1 : Cint.is_uint16 y) : Cint.to_uint16 (lor x y) = lor x y
axiom is_uint16_land (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint16 x) (fact1 : Cint.is_uint16 y) : Cint.to_uint16 (land x y) = land x y
axiom is_uint16_lsr (y : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : Cint.is_uint16 x) : Cint.to_uint16 (lsr x y) = lsr x y
axiom is_uint16_lsl1_inf (y : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : y < (16 : ℤ)) : Cint.to_uint16 (lsl (1 : ℤ) y) = lsl (1 : ℤ) y
axiom is_uint16_lsl1_sup (y : ℤ) (fact0 : (16 : ℤ) ≤ y) : Cint.to_uint16 (lsl (1 : ℤ) y) = (0 : ℤ)
axiom is_uint32_lxor (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint32 x) (fact1 : Cint.is_uint32 y) : Cint.to_uint32 (lxor x y) = lxor x y
axiom is_uint32_lor (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint32 x) (fact1 : Cint.is_uint32 y) : Cint.to_uint32 (lor x y) = lor x y
axiom is_uint32_land (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint32 x) (fact1 : Cint.is_uint32 y) : Cint.to_uint32 (land x y) = land x y
axiom is_uint32_lsr (y : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : Cint.is_uint32 x) : Cint.to_uint32 (lsr x y) = lsr x y
axiom is_uint32_lsl1_inf (y : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : y < (32 : ℤ)) : Cint.to_uint32 (lsl (1 : ℤ) y) = lsl (1 : ℤ) y
axiom is_uint32_lsl1_sup (y : ℤ) (fact0 : (32 : ℤ) ≤ y) : Cint.to_uint32 (lsl (1 : ℤ) y) = (0 : ℤ)
axiom is_uint64_lxor (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint64 x) (fact1 : Cint.is_uint64 y) : Cint.to_uint64 (lxor x y) = lxor x y
axiom is_uint64_lor (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint64 x) (fact1 : Cint.is_uint64 y) : Cint.to_uint64 (lor x y) = lor x y
axiom is_uint64_land (x : ℤ) (y : ℤ) (fact0 : Cint.is_uint64 x) (fact1 : Cint.is_uint64 y) : Cint.to_uint64 (land x y) = land x y
axiom is_uint64_lsr (y : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : Cint.is_uint64 x) : Cint.to_uint64 (lsr x y) = lsr x y
axiom is_uint64_lsl1_inf (y : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : y < (64 : ℤ)) : Cint.to_uint64 (lsl (1 : ℤ) y) = lsl (1 : ℤ) y
axiom is_uint64_lsl1_sup (y : ℤ) (fact0 : (64 : ℤ) ≤ y) : Cint.to_uint64 (lsl (1 : ℤ) y) = (0 : ℤ)
axiom is_sint_lnot (n : ℤ) (x : ℤ) (fact0 : Cint.is_sint n x) : Cint.to_sint n (lnot x) = lnot x
axiom is_sint_lxor (n : ℤ) (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint n x) (fact1 : Cint.is_sint n y) : Cint.to_sint n (lxor x y) = lxor x y
axiom is_sint_lor (n : ℤ) (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint n x) (fact1 : Cint.is_sint n y) : Cint.to_sint n (lor x y) = lor x y
axiom is_sint_land (n : ℤ) (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint n x) (fact1 : Cint.is_sint n y) : Cint.to_sint n (land x y) = land x y
axiom is_sint_lsr (y : ℤ) (n : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : Cint.is_sint n x) : Cint.to_sint n (lsr x y) = lsr x y
axiom is_sint_lsl1_inf (y : ℤ) (n : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : y < n) : Cint.to_sint n (lsl (1 : ℤ) y) = lsl (1 : ℤ) y
axiom is_sint_lsl1_sup (n : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ n) (fact1 : n < y) : Cint.to_sint n (lsl (1 : ℤ) y) = (0 : ℤ)
axiom is_sint8_lnot (x : ℤ) (fact0 : Cint.is_sint8 x) : Cint.to_sint8 (lnot x) = lnot x
axiom is_sint8_lxor (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint8 x) (fact1 : Cint.is_sint8 y) : Cint.to_sint8 (lxor x y) = lxor x y
axiom is_sint8_lor (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint8 x) (fact1 : Cint.is_sint8 y) : Cint.to_sint8 (lor x y) = lor x y
axiom is_sint8_land (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint8 x) (fact1 : Cint.is_sint8 y) : Cint.to_sint8 (land x y) = land x y
axiom is_sint8_lsr (y : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : Cint.is_sint8 x) : Cint.to_sint8 (lsr x y) = lsr x y
axiom is_sint8_lsl1 : lsl (1 : ℤ) (7 : ℤ) = (128 : ℤ)
axiom is_sint8_lsl1_inf (y : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : y < (7 : ℤ)) : Cint.to_sint8 (lsl (1 : ℤ) y) = lsl (1 : ℤ) y
axiom is_sint8_lsl1_sup (y : ℤ) (fact0 : (8 : ℤ) ≤ y) : Cint.to_sint8 (lsl (1 : ℤ) y) = (0 : ℤ)
axiom is_sint16_lnot (x : ℤ) (fact0 : Cint.is_sint16 x) : Cint.to_sint16 (lnot x) = lnot x
axiom is_sint16_lxor (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint16 x) (fact1 : Cint.is_sint16 y) : Cint.to_sint16 (lxor x y) = lxor x y
axiom is_sint16_lor (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint16 x) (fact1 : Cint.is_sint16 y) : Cint.to_sint16 (lor x y) = lor x y
axiom is_sint16_land (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint16 x) (fact1 : Cint.is_sint16 y) : Cint.to_sint16 (land x y) = land x y
axiom is_sint16_lsr (y : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : Cint.is_sint16 x) : Cint.to_sint16 (lsr x y) = lsr x y
axiom is_sint16_lsl1 : lsl (1 : ℤ) (15 : ℤ) = (32768 : ℤ)
axiom is_sint16_lsl1_inf (y : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : y < (15 : ℤ)) : Cint.to_sint16 (lsl (1 : ℤ) y) = lsl (1 : ℤ) y
axiom is_sint16_lsl1_sup (y : ℤ) (fact0 : (16 : ℤ) ≤ y) : Cint.to_sint16 (lsl (1 : ℤ) y) = (0 : ℤ)
axiom is_sint32_lnot (x : ℤ) (fact0 : Cint.is_sint32 x) : Cint.to_sint32 (lnot x) = lnot x
axiom is_sint32_lxor (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint32 x) (fact1 : Cint.is_sint32 y) : Cint.to_sint32 (lxor x y) = lxor x y
axiom is_sint32_lor (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint32 x) (fact1 : Cint.is_sint32 y) : Cint.to_sint32 (lor x y) = lor x y
axiom is_sint32_land (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint32 x) (fact1 : Cint.is_sint32 y) : Cint.to_sint32 (land x y) = land x y
axiom is_sint32_lsr (y : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : Cint.is_sint32 x) : Cint.to_sint32 (lsr x y) = lsr x y
axiom is_sint32_lsl1 : lsl (1 : ℤ) (31 : ℤ) = (2147483648 : ℤ)
axiom is_sint32_lsl1_inf (y : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : y < (31 : ℤ)) : Cint.to_sint32 (lsl (1 : ℤ) y) = lsl (1 : ℤ) y
axiom is_sint32_lsl1_sup (y : ℤ) (fact0 : (32 : ℤ) ≤ y) : Cint.to_sint32 (lsl (1 : ℤ) y) = (0 : ℤ)
axiom is_sint64_lnot (x : ℤ) (fact0 : Cint.is_sint64 x) : Cint.to_sint64 (lnot x) = lnot x
axiom is_sint64_lxor (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint64 x) (fact1 : Cint.is_sint64 y) : Cint.to_sint64 (lxor x y) = lxor x y
axiom is_sint64_lor (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint64 x) (fact1 : Cint.is_sint64 y) : Cint.to_sint64 (lor x y) = lor x y
axiom is_sint64_land (x : ℤ) (y : ℤ) (fact0 : Cint.is_sint64 x) (fact1 : Cint.is_sint64 y) : Cint.to_sint64 (land x y) = land x y
axiom is_sint64_lsr (y : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : Cint.is_sint64 x) : Cint.to_sint64 (lsr x y) = lsr x y
axiom is_sint64_lsl1 : lsl (1 : ℤ) (63 : ℤ) = (9223372036854775808 : ℤ)
axiom is_sint64_lsl1_inf (y : ℤ) (fact0 : (0 : ℤ) ≤ y) (fact1 : y < (63 : ℤ)) : Cint.to_sint64 (lsl (1 : ℤ) y) = lsl (1 : ℤ) y
axiom is_sint64_lsl1_sup (y : ℤ) (fact0 : (64 : ℤ) ≤ y) : Cint.to_sint64 (lsl (1 : ℤ) y) = (0 : ℤ)
axiom uint_land_range (x : ℤ) (y : ℤ) (fact0 : (0 : ℤ) ≤ x) : (0 : ℤ) ≤ land x y ∧ land x y ≤ x
axiom uint_lor_inf (x : ℤ) (y : ℤ) (fact0 : -(1 : ℤ) ≤ x) (fact1 : (0 : ℤ) ≤ y) : x ≤ lor x y
axiom sint_land_inf (x : ℤ) (y : ℤ) (fact0 : x ≤ (0 : ℤ)) (fact1 : y < (0 : ℤ)) : land x y ≤ x
axiom sint_lor_range (x : ℤ) (y : ℤ) (fact0 : x < (0 : ℤ)) : x ≤ lor x y ∧ lor x y < (0 : ℤ)
axiom is_uint_lor_distrib (n : ℤ) (x : ℤ) (y : ℤ) : Cint.is_uint n (lor x y) = (Cint.is_uint n x ∧ Cint.is_uint n y)
axiom lor_addition (x : ℤ) (y : ℤ) (fact0 : land x y = (0 : ℤ)) : x + y = lor x y
axiom lxor_addition (x : ℤ) (y : ℤ) (fact0 : land x y = (0 : ℤ)) : x + y = lxor x y
axiom to_uint_land_edge (n : ℤ) (x : ℤ) (fact0 : (0 : ℤ) ≤ n) : Cint.to_uint n x = land (lsl (1 : ℤ) n - (1 : ℤ)) x
end Cbits
namespace should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_10_goal22
theorem goal22 (a_1 : Memory.addr) (t_3 : Memory.addr -> ℤ) (t_4 : Memory.addr -> Memory.addr) (a : Memory.addr) (i : ℤ) (t_1 : Memory.addr -> ℤ) (t_2 : Memory.addr -> ℤ) (i_1 : ℤ) (i_2 : ℤ) (t : ℤ -> ℤ) : let a_2 : Memory.addr := Memory.shift a_1 (3 : ℤ); let x : ℤ := t_3 a_2; let a_3 : Memory.addr := Memory.shift a_1 (4 : ℤ); let a_4 : Memory.addr := t_4 a_3; let a_5 : Memory.addr := t_4 (Memory.shift a_4 (0 : ℤ)); let a_6 : Memory.addr := Memory.shift a_1 (1 : ℤ); let x_1 : ℤ := t_3 a_6; let x_2 : ℤ := t_3 (Memory.shift a_5 x_1); let a_7 : Memory.addr := Memory.shift a_1 (0 : ℤ); let a_8 : Memory.addr := Memory.shift a i; let a_9 : Memory.addr := t_4 a_7; let a_10 : Memory.addr := Memory.shift a_9 (1 : ℤ); let a_11 : Memory.addr := Memory.shift a_9 (0 : ℤ); let a_12 : Memory.addr := t_4 a_11; let a_13 : Memory.addr := A_schedule_cpumask.l_group_balance_mask a_12; let a_14 : Memory.addr := Memory.shift a_5 (0 : ℤ); let a_15 : Memory.addr := Memory.shift a_8 (0 : ℤ); let a_16 : Memory.addr := t_4 a_15; let a_17 : Memory.addr := Memory.shift a_16 (0 : ℤ); let a_18 : Memory.addr -> ℤ := Memory.havoc t_1 t_3 a_17 A_thread_variables_properties.l_size; let a_19 : Memory.addr := t_4 (Memory.shift a_13 (0 : ℤ)); let a_20 : Memory.addr -> ℤ := Memory.havoc t_2 t_3 a_17 A_thread_variables_properties.l_size; let a_21 : ℤ := a_20 (Memory.shift a_5 i_1); let a_22 : ℤ := a_20 (Memory.shift a_19 i_1); let a_23 : ℤ := a_20 a_10; let a_24 : Memory.addr := Memory.shift a_19 (0 : ℤ); ¬x = (2 : ℤ) → ¬x_2 = (0 : ℤ) → (0 : ℤ) ≤ i → i < A_thread_variables_properties.l_size → (0 : ℤ) ≤ i_2 → i_2 ≤ A_thread_variables_properties.l_size → (0 : ℤ) ≤ x_1 → x_1 < A_thread_variables_properties.l_size → Memory.region (Memory.addr.base a) ≤ (0 : ℤ) → Memory.region (Memory.addr.base a_1) ≤ (0 : ℤ) → Memory.framed t_4 → Memory.linked t → Cint.is_uint32 i → Cint.is_sint32 i_1 → Cint.is_sint32 i_2 → Memory.valid_rd t a_1 (5 : ℤ) → Cint.is_uint32 x → Cint.is_sint32 x_1 → Memory.valid_rd t a_3 (1 : ℤ) → Memory.valid_rd t a_6 (1 : ℤ) → Memory.valid_rd t a_2 (1 : ℤ) → Memory.valid_rd t a_7 (1 : ℤ) → Memory.valid_rd t a_8 (1 : ℤ) → Memory.valid_rd t a_4 (1 : ℤ) → Memory.valid_rd t (t_4 (Memory.shift a_1 (2 : ℤ))) (2 : ℤ) → Memory.valid_rd t a_9 (2 : ℤ) → Cint.is_sint32 (t_3 a_10) → Memory.valid_rd t a_11 (1 : ℤ) → Memory.valid_rd t a_12 (1 : ℤ) → Memory.valid_rd t a_13 (1 : ℤ) → Cint.is_uint8 x_2 → Memory.valid_rd t a_14 A_thread_variables_properties.l_size → Memory.valid_rw t a_17 A_thread_variables_properties.l_size → Cint.is_uint8 (a_18 (Memory.shift a_5 (-(1 : ℤ)))) → Cint.is_uint8 (a_18 (Memory.shift a_19 (-(1 : ℤ)))) → Cint.is_uint8 a_21 → Cint.is_uint8 a_22 → Cint.is_sint32 (a_18 a_10) → Cint.is_sint32 a_23 → Memory.valid_rd t a_24 A_thread_variables_properties.l_size → Memory.separated a_17 A_thread_variables_properties.l_size a_24 A_thread_variables_properties.l_size → (¬Cbits.land (7 : ℤ) a_23 = (0 : ℤ) → i_1 = -(1 : ℤ)) → (¬i_1 = -(1 : ℤ) → ¬A_schedule_cpumask.l_idle_cpu i_1 = (0 : ℤ) ∧ ¬a_21 = (0 : ℤ) ∧ ¬a_22 = (0 : ℤ) ∧ (0 : ℤ) ≤ i_1 ∧ i_1 < A_thread_variables_properties.l_size) → (i_1 = -(1 : ℤ) → (∀(i_3 : ℤ), ¬a_20 (Memory.shift a_19 i_3) = (0 : ℤ) → (0 : ℤ) ≤ i_3 → i_3 < A_thread_variables_properties.l_size → ¬a_20 (Memory.shift a_16 i_3) = (0 : ℤ))) → (¬i_1 = -(1 : ℤ) → (∀(i_3 : ℤ), ¬a_20 (Memory.shift a_5 i_3) = (0 : ℤ) → ¬a_20 (Memory.shift a_19 i_3) = (0 : ℤ) → (0 : ℤ) ≤ i_3 → i_3 < i_1 → i_3 < A_thread_variables_properties.l_size → A_schedule_cpumask.l_idle_cpu i_3 = (0 : ℤ))) → (i_1 = -(1 : ℤ) → (∀(i_3 : ℤ), ¬a_20 (Memory.shift a_5 i_3) = (0 : ℤ) → ¬a_20 (Memory.shift a_19 i_3) = (0 : ℤ) → (0 : ℤ) ≤ i_3 → i_3 < i_2 → i_3 < A_thread_variables_properties.l_size → A_schedule_cpumask.l_idle_cpu i_3 = (0 : ℤ))) → (¬i_1 = -(1 : ℤ) → (∀(i_3 : ℤ), ¬a_20 (Memory.shift a_5 i_3) = (0 : ℤ) → ¬a_20 (Memory.shift a_19 i_3) = (0 : ℤ) → (0 : ℤ) ≤ i_3 → i_1 ≤ i_3 → i_3 < i_2 → i_3 < A_thread_variables_properties.l_size → ¬A_schedule_cpumask.p_idle_core t_4 a_20 i_3)) → (¬i_1 = -(1 : ℤ) → (∀(i_3 : ℤ), ¬a_20 (Memory.shift a_19 i_3) = (0 : ℤ) → (0 : ℤ) ≤ i_3 → i_3 < A_thread_variables_properties.l_size → ¬a_20 (Memory.shift a_16 i_3) = (0 : ℤ) ∨ ¬A_schedule_cpumask.p_idle_core t_4 a_20 i_3)) → (∀(i_3 : ℤ), (0 : ℤ) ≤ i_3 → i_3 < A_thread_variables_properties.l_size → Memory.separated a_14 A_thread_variables_properties.l_size (Memory.shift (t_4 (Memory.shift (Memory.shift a i_3) (0 : ℤ))) (0 : ℤ)) A_thread_variables_properties.l_size) → (∀(i_3 : ℤ), let a_25 : Memory.addr := Memory.shift a i_3; (0 : ℤ) ≤ i_3 → i_3 < A_thread_variables_properties.l_size → Memory.valid_rd t a_25 (1 : ℤ) ∧ Memory.valid_rw t (Memory.shift (t_4 (Memory.shift a_25 (0 : ℤ))) (0 : ℤ)) A_thread_variables_properties.l_size) → (∀(i_3 : ℤ), (0 : ℤ) ≤ i_3 → i_3 < A_thread_variables_properties.l_size → (¬a_18 (Memory.shift a_19 i_3) = (0 : ℤ)) = (¬a_18 (Memory.shift a_16 i_3) = (0 : ℤ))) → (∀(i_3 : ℤ), ¬a_20 (Memory.shift a_16 i_3) = (0 : ℤ) → (0 : ℤ) ≤ i_3 → i_3 < A_thread_variables_properties.l_size → ¬a_20 (Memory.shift a_19 i_3) = (0 : ℤ)) → (∀(a_25 : Memory.addr), let a_26 : Memory.addr := A_schedule_cpumask.l_sched_group_cpus a_25; let a_27 : Memory.addr := Memory.shift (t_4 (Memory.shift a_26 (0 : ℤ))) (0 : ℤ); Memory.valid_rd t a_26 (1 : ℤ) ∧ Memory.valid_rd t a_27 A_thread_variables_properties.l_size ∧ (∀(i_3 : ℤ), (0 : ℤ) ≤ i_3 → i_3 < A_thread_variables_properties.l_size → Memory.separated a_27 A_thread_variables_properties.l_size (Memory.shift (t_4 (Memory.shift (Memory.shift a i_3) (0 : ℤ))) (0 : ℤ)) A_thread_variables_properties.l_size)) → (∀(a_25 : Memory.addr), let a_26 : Memory.addr := A_schedule_cpumask.l_sched_group_mask a_25; let a_27 : Memory.addr := Memory.shift (t_4 (Memory.shift a_26 (0 : ℤ))) (0 : ℤ); Memory.valid_rd t a_26 (1 : ℤ) ∧ Memory.valid_rd t a_27 A_thread_variables_properties.l_size ∧ (∀(i_3 : ℤ), (0 : ℤ) ≤ i_3 → i_3 < A_thread_variables_properties.l_size → Memory.separated a_27 A_thread_variables_properties.l_size (Memory.shift (t_4 (Memory.shift (Memory.shift a i_3) (0 : ℤ))) (0 : ℤ)) A_thread_variables_properties.l_size)) → (∀(a_25 : Memory.addr), let a_26 : Memory.addr := A_schedule_cpumask.l_group_balance_mask a_25; let a_27 : Memory.addr := Memory.shift (t_4 (Memory.shift a_26 (0 : ℤ))) (0 : ℤ); Memory.valid_rd t a_26 (1 : ℤ) ∧ Memory.valid_rd t a_27 A_thread_variables_properties.l_size ∧ (∀(i_3 : ℤ), (0 : ℤ) ≤ i_3 → i_3 < A_thread_variables_properties.l_size → Memory.separated a_27 A_thread_variables_properties.l_size (Memory.shift (t_4 (Memory.shift (Memory.shift a i_3) (0 : ℤ))) (0 : ℤ)) A_thread_variables_properties.l_size)) → (∀(i_3 : ℤ), let a_25 : Memory.addr := A_schedule_cpumask.l_cpu_smt_mask i_3; let a_26 : Memory.addr := Memory.shift (t_4 (Memory.shift a_25 (0 : ℤ))) (0 : ℤ); (0 : ℤ) ≤ i_3 → i_3 < A_thread_variables_properties.l_size → Memory.valid_rd t a_25 (1 : ℤ) ∧ Memory.valid_rd t a_26 A_thread_variables_properties.l_size ∧ (∀(i_4 : ℤ), (0 : ℤ) ≤ i_4 → i_4 < A_thread_variables_properties.l_size → Memory.separated a_26 A_thread_variables_properties.l_size (Memory.shift (t_4 (Memory.shift (Memory.shift a i_4) (0 : ℤ))) (0 : ℤ)) A_thread_variables_properties.l_size)) → Memory.valid_rd t a_15 (1 : ℤ)
  := sorry
end should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_10_goal22
