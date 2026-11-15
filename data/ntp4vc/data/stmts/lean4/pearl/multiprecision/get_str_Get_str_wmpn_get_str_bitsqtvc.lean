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
namespace MapEq
noncomputable def map_eq_sub {α : Type} [Inhabited α] (a1 : ℤ -> α) (a2 : ℤ -> α) (l : ℤ) (u : ℤ) := ∀(i : ℤ), l ≤ i ∧ i < u → a1 i = a2 i
end MapEq
namespace Unsigned
axiom t : Type
axiom inhabited_axiom_t : Inhabited t
attribute [instance] inhabited_axiom_t
axiom max : ℤ
axiom to_int : t -> ℤ
noncomputable def in_bounds (n : ℤ) := (0 : ℤ) ≤ n ∧ n ≤ max
axiom to_int_in_bounds (n : t) : in_bounds (to_int n)
axiom extensionality (x : t) (y : t) (fact0 : to_int x = to_int y) : x = y
axiom zero_unsigned : t
axiom zero_unsigned_is_zero : to_int zero_unsigned = (0 : ℤ)
axiom radix : ℤ
axiom radix_def : radix = max + (1 : ℤ)
end Unsigned
namespace C
noncomputable def in_us_bounds (n : ℤ) := (0 : ℤ) ≤ n ∧ n ≤ (4294967295 : ℤ)
noncomputable def in_bounds (n : ℤ) := -(2147483648 : ℤ) ≤ n ∧ n ≤ (2147483647 : ℤ)
axiom zone : Type
axiom inhabited_axiom_zone : Inhabited zone
attribute [instance] inhabited_axiom_zone
axiom null_zone : zone
axiom ptr : Type -> Type
axiom inhabited_axiom_ptr {α : Type} [Inhabited α] : Inhabited (ptr α)
attribute [instance] inhabited_axiom_ptr
axiom data :  {α : Type} -> [Inhabited α] -> ptr α -> List α
axiom offset :  {α : Type} -> [Inhabited α] -> ptr α -> ℤ
axiom min :  {α : Type} -> [Inhabited α] -> ptr α -> ℤ
axiom max :  {α : Type} -> [Inhabited α] -> ptr α -> ℤ
axiom writable :  {α : Type} -> [Inhabited α] -> ptr α -> Bool
axiom zone1 :  {α : Type} -> [Inhabited α] -> ptr α -> zone
noncomputable def plength {α : Type} [Inhabited α] (p : ptr α) := Int.ofNat (List.length (data p))
noncomputable def pelts {α : Type} [Inhabited α] (p : ptr α) := getElem! (data p) ∘ Int.toNat
axiom is_not_null :  {α : Type} -> [Inhabited α] -> ptr α -> Prop
axiom is_not_null'spec {α : Type} [Inhabited α] (p : ptr α) : is_not_null p = (¬zone1 p = null_zone)
noncomputable def valid_ptr_shift {α : Type} [Inhabited α] (p : ptr α) (i : ℤ) := min p ≤ offset p + i ∧ offset p + i < max p
noncomputable def valid {α : Type} [Inhabited α] (p : ptr α) (sz : ℤ) := in_bounds sz ∧ (0 : ℤ) ≤ sz ∧ ((0 : ℤ) ≤ min p ∧ min p ≤ offset p) ∧ offset p + sz ≤ max p ∧ max p ≤ plength p
axiom valid_itv_to_shift {α : Type} [Inhabited α] (p : ptr α) (sz : ℤ) (i : ℤ) (fact0 : valid p sz) (fact1 : (0 : ℤ) ≤ i) (fact2 : i < sz) : valid_ptr_shift p i
end C
namespace UChar
axiom cast_mem : Type
axiom cast_mem_inhabited : Inhabited cast_mem
attribute [instance] cast_mem_inhabited
axiom mi : cast_mem -> ℤ
axiom ma : cast_mem -> ℤ
axiom z : cast_mem -> C.zone
axiom l : cast_mem -> ℤ
axiom ok : cast_mem -> Bool
end UChar
namespace Config
end Config
namespace Types
axiom limb : Type
axiom inhabited_axiom_limb : Inhabited limb
attribute [instance] inhabited_axiom_limb
axiom t : Type
axiom inhabited_axiom_t : Inhabited t
attribute [instance] inhabited_axiom_t
end Types
namespace Int32Eq
end Int32Eq
namespace UInt64Eq
end UInt64Eq
namespace Lemmas
noncomputable def map_eq_sub_shift {α : Type} [Inhabited α] (x : ℤ -> α) (y : ℤ -> α) (xi : ℤ) (yi : ℤ) (sz : ℤ) := ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < sz → x (xi + i) = y (yi + i)
axiom value_sub : (ℤ -> BitVec 64) -> ℤ -> ℤ -> ℤ
axiom value_sub'def (n : ℤ) (m : ℤ) (x : ℤ -> BitVec 64) : if n < m then value_sub x n m = BitVec.toUInt (x n) + ((18446744073709551615 : ℤ) + (1 : ℤ)) * value_sub x (n + (1 : ℤ)) m else value_sub x n m = (0 : ℤ)
noncomputable def value (x : C.ptr (BitVec 64)) (sz : ℤ) := value_sub (C.pelts x) (C.offset x) (C.offset x + sz)
end Lemmas
namespace Compare
noncomputable def compare_int (x : ℤ) (y : ℤ) := if x < y then -(1 : ℤ) else if x = y then (0 : ℤ) else (1 : ℤ)
end Compare
namespace Valuation
axiom valuation : ℤ -> ℤ -> ℤ
axiom valuation'def (p : ℤ) (n : ℤ) (fact0 : (1 : ℤ) < p) (fact1 : (1 : ℤ) ≤ n) : if Int.tmod n p = (0 : ℤ) then valuation n p = valuation (Int.tdiv n p) p + (1 : ℤ) else valuation n p = (0 : ℤ)
axiom valuation'spec'0 (p : ℤ) (n : ℤ) (fact0 : (1 : ℤ) < p) (fact1 : (1 : ℤ) ≤ n) : (0 : ℤ) ≤ valuation n p
axiom valuation'spec (p : ℤ) (n : ℤ) (fact0 : (1 : ℤ) < p) (fact1 : (1 : ℤ) ≤ n) : HPow.hPow p (Int.toNat (valuation n p)) ∣  n
end Valuation
namespace Alias
axiom mem : Type
axiom inhabited_axiom_mem : Inhabited mem
attribute [instance] inhabited_axiom_mem
axiom zr : mem -> C.zone
axiom zx : mem -> C.zone
axiom zy : mem -> C.zone
axiom mr : mem -> BitVec 32
axiom mx : mem -> BitVec 32
axiom my : mem -> BitVec 32
axiom lr : mem -> BitVec 32
axiom lx : mem -> BitVec 32
axiom ly : mem -> BitVec 32
axiom ok : mem -> Bool
noncomputable def identical (p1 : C.ptr (BitVec 64)) (p2 : C.ptr (BitVec 64)) := C.data p1 = C.data p2 ∧ C.offset p1 = C.offset p2 ∧ C.min p1 = C.min p2 ∧ C.max p1 = C.max p2 ∧ C.zone1 p1 = C.zone1 p2
end Alias
namespace Util
end Util
namespace UtilOld
end UtilOld
namespace Add
end Add
namespace AddOld
end AddOld
namespace SubOld
end SubOld
namespace Mul
end Mul
namespace Mul_basecase
end Mul_basecase
namespace LogicalUtil
end LogicalUtil
namespace Logical
end Logical
namespace LogicalOld
end LogicalOld
namespace Div
noncomputable def reciprocal (v : BitVec 64) (d : BitVec 64) := BitVec.toUInt v = (((18446744073709551615 : ℤ) + (1 : ℤ)) * ((18446744073709551615 : ℤ) + (1 : ℤ)) - (1 : ℤ)) / BitVec.toUInt d - ((18446744073709551615 : ℤ) + (1 : ℤ))
noncomputable def reciprocal_3by2 (v : BitVec 64) (dh : BitVec 64) (dl : BitVec 64) := BitVec.toUInt v = (((18446744073709551615 : ℤ) + (1 : ℤ)) * ((18446744073709551615 : ℤ) + (1 : ℤ)) * ((18446744073709551615 : ℤ) + (1 : ℤ)) - (1 : ℤ)) / (BitVec.toUInt dl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt dh) - ((18446744073709551615 : ℤ) + (1 : ℤ))
noncomputable def normalized (x : C.ptr (BitVec 64)) (sz : BitVec 32) := C.valid x (BitVec.toInt sz) ∧ ((18446744073709551615 : ℤ) + (1 : ℤ)) / (2 : ℤ) ≤ BitVec.toUInt (C.pelts x (C.offset x + BitVec.toInt sz - (1 : ℤ)))
end Div
namespace Add_1
end Add_1
namespace Sub_1
end Sub_1
namespace Toom
end Toom
namespace Powm
noncomputable def redc (ur : ℤ) (u : ℤ) (n : ℤ) (m : ℤ) := ur % m = HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat n) * u % m
noncomputable def valueb (p : C.ptr (BitVec 64)) (nbits : ℤ) := if nbits < (0 : ℤ) then (0 : ℤ) else let i : ℤ := nbits / (64 : ℤ); Lemmas.value p i + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat i) * (BitVec.toUInt (C.pelts p (C.offset p + i)) % HPow.hPow (2 : ℤ) (Int.toNat (nbits - (64 : ℤ) * i)))
end Powm
namespace String_lemmas
noncomputable def in_base (b : ℤ) (x : ℤ -> BitVec 8) (n : ℤ) (m : ℤ) := ∀(i : ℤ), n ≤ i ∧ i < m → (0 : ℤ) ≤ BitVec.toInt (x i) ∧ BitVec.toInt (x i) < b
axiom svalue_le_sub : ℤ -> (ℤ -> BitVec 8) -> ℤ -> ℤ -> ℤ
axiom svalue_le_sub'def (n : ℤ) (m : ℤ) (b : ℤ) (x : ℤ -> BitVec 8) : if n < m then svalue_le_sub b x n m = BitVec.toInt (x n) + b * svalue_le_sub b x (n + (1 : ℤ)) m else svalue_le_sub b x n m = (0 : ℤ)
noncomputable def string_in_base (b : ℤ) (p : C.ptr (BitVec 8)) := in_base b (C.pelts p) (C.min p) (C.max p)
noncomputable def svalue_le (b : ℤ) (x : C.ptr (BitVec 8)) (sz : ℤ) := svalue_le_sub b (C.pelts x) (C.offset x) (C.offset x + sz)
axiom svalue_sub : ℤ -> (ℤ -> BitVec 8) -> ℤ -> ℤ -> ℤ
axiom svalue_sub'def (n : ℤ) (m : ℤ) (b : ℤ) (x : ℤ -> BitVec 8) : if n < m then svalue_sub b x n m = BitVec.toInt (x (m - (1 : ℤ))) + b * svalue_sub b x n (m - (1 : ℤ)) else svalue_sub b x n m = (0 : ℤ)
noncomputable def svalue (b : ℤ) (x : C.ptr (BitVec 8)) (sz : ℤ) := svalue_sub b (C.pelts x) (C.offset x) (C.offset x + sz)
end String_lemmas
namespace BaseInfo
axiom wmpn_base_info : Type
axiom inhabited_axiom_wmpn_base_info : Inhabited wmpn_base_info
attribute [instance] inhabited_axiom_wmpn_base_info
axiom b : wmpn_base_info -> ℤ
axiom exp : wmpn_base_info -> BitVec 32
axiom bb : wmpn_base_info -> BitVec 64
axiom wmpn_base_info'invariant (self : wmpn_base_info) : (2 : ℤ) ≤ b self ∧ b self ≤ (256 : ℤ) ∧ BitVec.toUInt (bb self) < (18446744073709551615 : ℤ) + (1 : ℤ) ∧ (18446744073709551615 : ℤ) + (1 : ℤ) ≤ BitVec.toUInt (bb self) * b self ∧ (7 : ℤ) ≤ BitVec.toUInt (exp self) ∧ BitVec.toUInt (exp self) ≤ (63 : ℤ) ∧ BitVec.toUInt (bb self) = HPow.hPow (b self) (Int.toNat (BitVec.toUInt (exp self)))
noncomputable def wmpn_base_info'eq (a : wmpn_base_info) (b1 : wmpn_base_info) := b a = b b1 ∧ exp a = exp b1 ∧ bb a = bb b1
axiom wmpn_base_info'inj (a : wmpn_base_info) (b1 : wmpn_base_info) (fact0 : wmpn_base_info'eq a b1) : a = b1
end BaseInfo
namespace get_str_Get_str_wmpn_get_str_bitsqtvc
theorem wmpn_get_str_bits'vc (un : BitVec 32) (up : C.ptr (BitVec 64)) (bits : BitVec 32) (sp : C.ptr (BitVec 8)) (ub : BitVec 32) (fact0 : (1 : ℤ) ≤ BitVec.toInt un) (fact1 : C.valid up (BitVec.toInt un)) (fact2 : (1 : ℤ) ≤ BitVec.toUInt bits) (fact3 : BitVec.toUInt bits ≤ (8 : ℤ)) (fact4 : C.valid sp ((BitVec.toInt ub + BitVec.toUInt bits - (1 : ℤ)) / BitVec.toUInt bits)) (fact5 : (0 : ℤ) ≤ BitVec.toInt ub) (fact6 : Lemmas.value up (BitVec.toInt un) < HPow.hPow (2 : ℤ) (Int.toNat (BitVec.toInt ub))) (fact7 : (0 : ℤ) < BitVec.toUInt (C.pelts up (C.offset up + BitVec.toInt un - (1 : ℤ)))) (fact8 : (64 : ℤ) * BitVec.toInt un + (7 : ℤ) ≤ (2147483647 : ℤ)) (fact9 : C.writable sp = true) : int'32_in_bounds (BitVec.toInt un - (1 : ℤ)) ∧ (∀(o1 : BitVec 32), BitVec.toInt o1 = BitVec.toInt un - (1 : ℤ) → (C.min up ≤ C.offset up + BitVec.toInt o1 ∧ C.offset up + BitVec.toInt o1 < C.max up) ∧ (let um : BitVec 64 := C.pelts up (C.offset up + BitVec.toInt o1); (0 : ℤ) < BitVec.toUInt um ∧ (∀(sb : BitVec 64), ((1 : ℤ) ≤ BitVec.toUInt sb ∧ BitVec.toUInt sb ≤ (64 : ℤ)) ∧ HPow.hPow (2 : ℤ) (Int.toNat (BitVec.toUInt sb - (1 : ℤ))) ≤ BitVec.toUInt um ∧ BitVec.toUInt um < HPow.hPow (2 : ℤ) (Int.toNat (BitVec.toUInt sb)) → BitVec.toUInt bits ≤ (2147483647 : ℤ) ∧ (∀(o2 : BitVec 32), BitVec.toInt o2 = BitVec.toUInt bits → BitVec.toUInt sb ≤ (2147483647 : ℤ) ∧ (∀(o3 : BitVec 32), BitVec.toInt o3 = BitVec.toUInt sb → int'32_in_bounds (BitVec.toInt un - (1 : ℤ)) ∧ (∀(o4 : BitVec 32), BitVec.toInt o4 = BitVec.toInt un - (1 : ℤ) → int'32_in_bounds ((64 : ℤ) * BitVec.toInt o4) ∧ (∀(o5 : BitVec 32), BitVec.toInt o5 = (64 : ℤ) * BitVec.toInt o4 → int'32_in_bounds (BitVec.toInt o5 + BitVec.toInt o3) ∧ (∀(o6 : BitVec 32), BitVec.toInt o6 = BitVec.toInt o5 + BitVec.toInt o3 → int'32_in_bounds (BitVec.toInt o6 + BitVec.toInt o2) ∧ (∀(o7 : BitVec 32), BitVec.toInt o7 = BitVec.toInt o6 + BitVec.toInt o2 → int'32_in_bounds (BitVec.toInt o7 - (1 : ℤ)) ∧ (∀(e : BitVec 32), BitVec.toInt e = BitVec.toInt o7 - (1 : ℤ) → BitVec.toUInt bits ≤ (2147483647 : ℤ) ∧ (∀(o8 : BitVec 32), BitVec.toInt o8 = BitVec.toUInt bits → (¬BitVec.toInt o8 = (0 : ℤ) ∧ int'32_in_bounds (Int.tdiv (BitVec.toInt e) (BitVec.toInt o8))) ∧ (∀(sn : BitVec 32), BitVec.toInt sn = Int.tdiv (BitVec.toInt e) (BitVec.toInt o8) → (∀(o9 : BitVec 64), BitVec.toUInt o9 = BitVec.toUInt bits → (((0 : ℤ) ≤ BitVec.toUInt o9 ∧ BitVec.toUInt o9 < (64 : ℤ)) ∧ HPow.hPow (2 : ℤ) (Int.toNat (BitVec.toUInt o9)) * BitVec.toUInt (1 : BitVec 64) ≤ (18446744073709551615 : ℤ)) ∧ (∀(b : BitVec 64), BitVec.toUInt b = HPow.hPow (2 : ℤ) (Int.toNat (BitVec.toUInt o9)) * BitVec.toUInt (1 : BitVec 64) → (((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ BitVec.toInt un) ∧ ((0 : ℤ) ≤ BitVec.toInt sn ∧ BitVec.toInt sn ≤ BitVec.toInt sn) ∧ (BitVec.toInt sn - BitVec.toInt sn) * BitVec.toUInt bits = (0 : ℤ) ∧ ((0 : ℤ) < BitVec.toInt sn → (0 : ℤ) = (64 : ℤ) * (0 : ℤ) + (0 : ℤ)) ∧ ((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) < (64 : ℤ) ∨ (0 : BitVec 32) = un) ∧ String_lemmas.in_base (BitVec.toUInt b) (C.pelts sp) (C.offset sp + BitVec.toInt sn) (C.offset sp + BitVec.toInt sn) ∧ (String_lemmas.svalue_sub (BitVec.toUInt b) (C.pelts sp) (C.offset sp + BitVec.toInt sn) (C.offset sp + BitVec.toInt sn) = Powm.valueb up (0 : ℤ) ∧ (0 : ℤ) ≤ (64 : ℤ) * BitVec.toInt un ∨ BitVec.toInt sn = (0 : ℤ) ∧ String_lemmas.svalue (BitVec.toUInt b) sp (BitVec.toInt sn) = Lemmas.value up (BitVec.toInt un))) ∧ (∀(shift : BitVec 64) (j : BitVec 32) (i : BitVec 32) (sp1 : C.ptr (BitVec 8)), List.length (C.data sp1) = List.length (C.data sp) ∧ C.offset sp1 = C.offset sp ∧ C.min sp1 = C.min sp ∧ C.max sp1 = C.max sp ∧ C.writable sp1 = C.writable sp ∧ C.zone1 sp1 = C.zone1 sp → ((0 : ℤ) ≤ BitVec.toInt i ∧ BitVec.toInt i ≤ BitVec.toInt un) ∧ ((0 : ℤ) ≤ BitVec.toInt j ∧ BitVec.toInt j ≤ BitVec.toInt sn) ∧ ((0 : ℤ) < BitVec.toInt j → (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits = (64 : ℤ) * BitVec.toInt i + BitVec.toUInt shift) ∧ ((0 : ℤ) ≤ BitVec.toUInt shift ∧ BitVec.toUInt shift < (64 : ℤ) ∨ i = un) ∧ String_lemmas.in_base (BitVec.toUInt b) (C.pelts sp1) (C.offset sp1 + BitVec.toInt j) (C.offset sp1 + BitVec.toInt sn) ∧ (String_lemmas.svalue_sub (BitVec.toUInt b) (C.pelts sp1) (C.offset sp1 + BitVec.toInt j) (C.offset sp1 + BitVec.toInt sn) = Powm.valueb up ((BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits) ∧ (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits ≤ (64 : ℤ) * BitVec.toInt un ∨ BitVec.toInt j = (0 : ℤ) ∧ String_lemmas.svalue (BitVec.toUInt b) sp1 (BitVec.toInt sn) = Lemmas.value up (BitVec.toInt un)) ∧ (∀(k : ℤ), k < C.offset sp1 ∨ C.offset sp1 + BitVec.toInt sn ≤ k → C.pelts sp1 k = C.pelts sp k) → (if (0 : ℤ) < BitVec.toInt j then int'32_in_bounds (BitVec.toInt j - (1 : ℤ)) ∧ (∀(o10 : BitVec 32), BitVec.toInt o10 = BitVec.toInt j - (1 : ℤ) → (C.min up ≤ C.offset up + BitVec.toInt i ∧ C.offset up + BitVec.toInt i < C.max up) ∧ ((0 : ℤ) ≤ BitVec.toUInt shift ∧ BitVec.toUInt shift < (64 : ℤ)) ∧ (∀(o11 : BitVec 64), BitVec.toUInt o11 = BitVec.toUInt (C.pelts up (C.offset up + BitVec.toInt i)) / HPow.hPow (2 : ℤ) (Int.toNat (BitVec.toUInt shift)) → ¬HPow.hPow (2 : ℤ) (Int.toNat (BitVec.toUInt shift)) = (0 : ℤ) ∧ (∀(o12 : BitVec 64), BitVec.toUInt o12 = BitVec.toUInt bits → uint'64_in_bounds (BitVec.toUInt shift + BitVec.toUInt o12) ∧ (∀(o13 : BitVec 64), BitVec.toUInt o13 = BitVec.toUInt shift + BitVec.toUInt o12 → (if (64 : ℤ) ≤ BitVec.toUInt o13 then int'32_in_bounds (BitVec.toInt i + (1 : ℤ)) ∧ (∀(o14 : BitVec 32), BitVec.toInt o14 = BitVec.toInt i + (1 : ℤ) → (if BitVec.toInt o14 < BitVec.toInt un then uint'64_in_bounds (BitVec.toUInt o13 - (64 : ℤ)) ∧ (∀(o15 : BitVec 64), BitVec.toUInt o15 = BitVec.toUInt o13 - (64 : ℤ) → (C.min up ≤ C.offset up + BitVec.toInt o14 ∧ C.offset up + BitVec.toInt o14 < C.max up) ∧ (∀(o16 : BitVec 64), BitVec.toUInt o16 = BitVec.toUInt bits → uint'64_in_bounds (BitVec.toUInt o16 - BitVec.toUInt o15) ∧ (∀(o17 : BitVec 64), BitVec.toUInt o17 = BitVec.toUInt o16 - BitVec.toUInt o15 → ((0 : ℤ) ≤ BitVec.toUInt o17 ∧ BitVec.toUInt o17 < (64 : ℤ)) ∧ (∀(high : BitVec 64), BitVec.toUInt high = BitVec.toUInt (C.pelts up (C.offset up + BitVec.toInt o14)) * HPow.hPow (2 : ℤ) (Int.toNat (BitVec.toUInt o17)) % ((18446744073709551615 : ℤ) + (1 : ℤ)) → uint'64_in_bounds (BitVec.toUInt o11 + BitVec.toUInt high) ∧ (∀(o18 : BitVec 64), BitVec.toUInt o18 = BitVec.toUInt o11 + BitVec.toUInt high → (¬BitVec.toUInt b = (0 : ℤ) ∧ uint'64_in_bounds (Int.tmod (BitVec.toUInt o18) (BitVec.toUInt b))) ∧ (∀(sj : BitVec 64), BitVec.toUInt sj = Int.tmod (BitVec.toUInt o18) (BitVec.toUInt b) → ((0 : ℤ) ≤ BitVec.toUInt sj ∧ BitVec.toUInt sj ≤ (255 : ℤ)) ∧ (∀(o19 : BitVec 8), BitVec.toInt o19 = BitVec.toUInt sj → ((C.min sp1 ≤ C.offset sp1 + BitVec.toInt o10 ∧ C.offset sp1 + BitVec.toInt o10 < C.max sp1) ∧ C.writable sp1 = true) ∧ (∀(sp2 : C.ptr (BitVec 8)), List.length (C.data sp2) = List.length (C.data sp1) ∧ C.offset sp2 = C.offset sp1 ∧ C.min sp2 = C.min sp1 ∧ C.max sp2 = C.max sp1 ∧ C.writable sp2 = C.writable sp1 ∧ C.zone1 sp2 = C.zone1 sp1 → C.pelts sp2 = Function.update (C.pelts sp1) (C.offset sp2 + BitVec.toInt o10) o19 ∧ C.pelts sp2 (C.offset sp2 + BitVec.toInt o10) = o19 → BitVec.toInt o10 < BitVec.toInt j ∧ ((0 : ℤ) ≤ BitVec.toInt o14 ∧ BitVec.toInt o14 ≤ BitVec.toInt un) ∧ ((0 : ℤ) ≤ BitVec.toInt o10 ∧ BitVec.toInt o10 ≤ BitVec.toInt sn) ∧ (BitVec.toInt sn - BitVec.toInt o10) * BitVec.toUInt bits = (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits ∧ ((0 : ℤ) < BitVec.toInt o10 → (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits = (64 : ℤ) * BitVec.toInt o14 + BitVec.toUInt o15) ∧ ((0 : ℤ) ≤ BitVec.toUInt o15 ∧ BitVec.toUInt o15 < (64 : ℤ) ∨ o14 = un) ∧ String_lemmas.in_base (BitVec.toUInt b) (C.pelts sp2) (C.offset sp2 + BitVec.toInt o10) (C.offset sp2 + BitVec.toInt sn) ∧ (String_lemmas.svalue_sub (BitVec.toUInt b) (C.pelts sp2) (C.offset sp2 + BitVec.toInt o10) (C.offset sp2 + BitVec.toInt sn) = Powm.valueb up ((BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits) ∧ (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits ≤ (64 : ℤ) * BitVec.toInt un ∨ BitVec.toInt o10 = (0 : ℤ) ∧ String_lemmas.svalue (BitVec.toUInt b) sp2 (BitVec.toInt sn) = Lemmas.value up (BitVec.toInt un)) ∧ (∀(k : ℤ), k < C.offset sp2 ∨ C.offset sp2 + BitVec.toInt sn ≤ k → C.pelts sp2 k = C.pelts sp k))))))))) else (¬BitVec.toUInt b = (0 : ℤ) ∧ uint'64_in_bounds (Int.tmod (BitVec.toUInt o11) (BitVec.toUInt b))) ∧ (∀(sj : BitVec 64), BitVec.toUInt sj = Int.tmod (BitVec.toUInt o11) (BitVec.toUInt b) → ((0 : ℤ) ≤ BitVec.toUInt sj ∧ BitVec.toUInt sj ≤ (255 : ℤ)) ∧ (∀(o15 : BitVec 8), BitVec.toInt o15 = BitVec.toUInt sj → ((C.min sp1 ≤ C.offset sp1 + BitVec.toInt o10 ∧ C.offset sp1 + BitVec.toInt o10 < C.max sp1) ∧ C.writable sp1 = true) ∧ (∀(sp2 : C.ptr (BitVec 8)), List.length (C.data sp2) = List.length (C.data sp1) ∧ C.offset sp2 = C.offset sp1 ∧ C.min sp2 = C.min sp1 ∧ C.max sp2 = C.max sp1 ∧ C.writable sp2 = C.writable sp1 ∧ C.zone1 sp2 = C.zone1 sp1 → C.pelts sp2 = Function.update (C.pelts sp1) (C.offset sp2 + BitVec.toInt o10) o15 ∧ C.pelts sp2 (C.offset sp2 + BitVec.toInt o10) = o15 → BitVec.toInt o10 < BitVec.toInt j ∧ ((0 : ℤ) ≤ BitVec.toInt o14 ∧ BitVec.toInt o14 ≤ BitVec.toInt un) ∧ ((0 : ℤ) ≤ BitVec.toInt o10 ∧ BitVec.toInt o10 ≤ BitVec.toInt sn) ∧ (BitVec.toInt sn - BitVec.toInt o10) * BitVec.toUInt bits = (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits ∧ ((0 : ℤ) < BitVec.toInt o10 → (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits = (64 : ℤ) * BitVec.toInt o14 + BitVec.toUInt o13) ∧ ((0 : ℤ) ≤ BitVec.toUInt o13 ∧ BitVec.toUInt o13 < (64 : ℤ) ∨ o14 = un) ∧ String_lemmas.in_base (BitVec.toUInt b) (C.pelts sp2) (C.offset sp2 + BitVec.toInt o10) (C.offset sp2 + BitVec.toInt sn) ∧ (String_lemmas.svalue_sub (BitVec.toUInt b) (C.pelts sp2) (C.offset sp2 + BitVec.toInt o10) (C.offset sp2 + BitVec.toInt sn) = Powm.valueb up ((BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits) ∧ (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits ≤ (64 : ℤ) * BitVec.toInt un ∨ BitVec.toInt o10 = (0 : ℤ) ∧ String_lemmas.svalue (BitVec.toUInt b) sp2 (BitVec.toInt sn) = Lemmas.value up (BitVec.toInt un)) ∧ (∀(k : ℤ), k < C.offset sp2 ∨ C.offset sp2 + BitVec.toInt sn ≤ k → C.pelts sp2 k = C.pelts sp k)))))) else (¬BitVec.toUInt b = (0 : ℤ) ∧ uint'64_in_bounds (Int.tmod (BitVec.toUInt o11) (BitVec.toUInt b))) ∧ (∀(sj : BitVec 64), BitVec.toUInt sj = Int.tmod (BitVec.toUInt o11) (BitVec.toUInt b) → ((0 : ℤ) ≤ BitVec.toUInt sj ∧ BitVec.toUInt sj ≤ (255 : ℤ)) ∧ (∀(o14 : BitVec 8), BitVec.toInt o14 = BitVec.toUInt sj → ((C.min sp1 ≤ C.offset sp1 + BitVec.toInt o10 ∧ C.offset sp1 + BitVec.toInt o10 < C.max sp1) ∧ C.writable sp1 = true) ∧ (∀(sp2 : C.ptr (BitVec 8)), List.length (C.data sp2) = List.length (C.data sp1) ∧ C.offset sp2 = C.offset sp1 ∧ C.min sp2 = C.min sp1 ∧ C.max sp2 = C.max sp1 ∧ C.writable sp2 = C.writable sp1 ∧ C.zone1 sp2 = C.zone1 sp1 → C.pelts sp2 = Function.update (C.pelts sp1) (C.offset sp2 + BitVec.toInt o10) o14 ∧ C.pelts sp2 (C.offset sp2 + BitVec.toInt o10) = o14 → BitVec.toInt o10 < BitVec.toInt j ∧ ((0 : ℤ) ≤ BitVec.toInt i ∧ BitVec.toInt i ≤ BitVec.toInt un) ∧ ((0 : ℤ) ≤ BitVec.toInt o10 ∧ BitVec.toInt o10 ≤ BitVec.toInt sn) ∧ (BitVec.toInt sn - BitVec.toInt o10) * BitVec.toUInt bits = (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits ∧ ((0 : ℤ) < BitVec.toInt o10 → (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits = (64 : ℤ) * BitVec.toInt i + BitVec.toUInt o13) ∧ ((0 : ℤ) ≤ BitVec.toUInt o13 ∧ BitVec.toUInt o13 < (64 : ℤ) ∨ i = un) ∧ String_lemmas.in_base (BitVec.toUInt b) (C.pelts sp2) (C.offset sp2 + BitVec.toInt o10) (C.offset sp2 + BitVec.toInt sn) ∧ (String_lemmas.svalue_sub (BitVec.toUInt b) (C.pelts sp2) (C.offset sp2 + BitVec.toInt o10) (C.offset sp2 + BitVec.toInt sn) = Powm.valueb up ((BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits) ∧ (BitVec.toInt sn - BitVec.toInt j) * BitVec.toUInt bits + BitVec.toUInt bits ≤ (64 : ℤ) * BitVec.toInt un ∨ BitVec.toInt o10 = (0 : ℤ) ∧ String_lemmas.svalue (BitVec.toUInt b) sp2 (BitVec.toInt sn) = Lemmas.value up (BitVec.toInt un)) ∧ (∀(k : ℤ), k < C.offset sp2 ∨ C.offset sp2 + BitVec.toInt sn ≤ k → C.pelts sp2 k = C.pelts sp k))))))))) else (0 : ℤ) ≤ BitVec.toInt sn ∧ (∀(result : BitVec 32), BitVec.toUInt result = BitVec.toInt sn → String_lemmas.in_base (HPow.hPow (2 : ℤ) (Int.toNat (BitVec.toUInt bits))) (C.pelts sp1) (C.offset sp1) (C.offset sp1 + BitVec.toUInt result) ∧ String_lemmas.svalue (HPow.hPow (2 : ℤ) (Int.toNat (BitVec.toUInt bits))) sp1 (BitVec.toUInt result) = Lemmas.value up (BitVec.toInt un) ∧ ((0 : ℤ) < BitVec.toUInt result ∧ BitVec.toUInt result ≤ (BitVec.toInt ub + BitVec.toUInt bits - (1 : ℤ)) / BitVec.toUInt bits) ∧ (0 : ℤ) < BitVec.toInt (C.pelts sp1 (C.offset sp1)) ∧ (∀(j1 : ℤ), j1 < C.offset sp1 ∨ C.offset sp1 + (BitVec.toInt ub + BitVec.toUInt bits - (1 : ℤ)) / BitVec.toUInt bits ≤ j1 → C.pelts sp1 j1 = C.pelts sp j1))))))))))))))))))
  := sorry
end get_str_Get_str_wmpn_get_str_bitsqtvc
