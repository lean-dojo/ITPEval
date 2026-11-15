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
namespace LogicalUtil
end LogicalUtil
namespace LogicalOld
end LogicalOld
namespace Mul
end Mul
namespace div_Div_div_sb_qrqtvc
noncomputable def reciprocal (v : BitVec 64) (d : BitVec 64) := BitVec.toUInt v = (((18446744073709551615 : ℤ) + (1 : ℤ)) * ((18446744073709551615 : ℤ) + (1 : ℤ)) - (1 : ℤ)) / BitVec.toUInt d - ((18446744073709551615 : ℤ) + (1 : ℤ))
noncomputable def reciprocal_3by2 (v : BitVec 64) (dh : BitVec 64) (dl : BitVec 64) := BitVec.toUInt v = (((18446744073709551615 : ℤ) + (1 : ℤ)) * ((18446744073709551615 : ℤ) + (1 : ℤ)) * ((18446744073709551615 : ℤ) + (1 : ℤ)) - (1 : ℤ)) / (BitVec.toUInt dl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt dh) - ((18446744073709551615 : ℤ) + (1 : ℤ))
noncomputable def normalized (x : C.ptr (BitVec 64)) (sz : BitVec 32) := C.valid x (BitVec.toInt sz) ∧ ((18446744073709551615 : ℤ) + (1 : ℤ)) / (2 : ℤ) ≤ BitVec.toUInt (C.pelts x (C.offset x + BitVec.toInt sz - (1 : ℤ)))
theorem div_sb_qr'vc (sy : BitVec 32) (sx : BitVec 32) (x : C.ptr (BitVec 64)) (y : C.ptr (BitVec 64)) (q : C.ptr (BitVec 64)) (fact0 : (3 : ℤ) ≤ BitVec.toInt sy) (fact1 : BitVec.toInt sy ≤ BitVec.toInt sx) (fact2 : C.valid x (BitVec.toInt sx)) (fact3 : C.valid y (BitVec.toInt sy)) (fact4 : C.valid q (BitVec.toInt sx - BitVec.toInt sy)) (fact5 : C.writable q = true) (fact6 : C.writable x = true) (fact7 : normalized y sy) : int'32_in_bounds (BitVec.toInt sx - (2 : ℤ)) ∧ (∀(o1 : BitVec 32), BitVec.toInt o1 = BitVec.toInt sx - (2 : ℤ) → (C.min x ≤ C.offset x + BitVec.toInt o1 ∧ C.offset x + BitVec.toInt o1 ≤ C.max x) ∧ (∀(o2 : C.ptr (BitVec 64)), C.offset o2 = C.offset x + BitVec.toInt o1 ∧ C.plength o2 = C.plength x ∧ C.pelts o2 = C.pelts x ∧ C.data o2 = C.data x ∧ C.min o2 = C.min x ∧ C.max o2 = C.max x ∧ C.zone1 o2 = C.zone1 x ∧ C.writable o2 = C.writable x → int'32_in_bounds (BitVec.toInt sx - BitVec.toInt sy) ∧ (∀(o3 : BitVec 32), BitVec.toInt o3 = BitVec.toInt sx - BitVec.toInt sy → (C.min q ≤ C.offset q + BitVec.toInt o3 ∧ C.offset q + BitVec.toInt o3 ≤ C.max q) ∧ (∀(o4 : C.ptr (BitVec 64)), C.offset o4 = C.offset q + BitVec.toInt o3 ∧ C.plength o4 = C.plength q ∧ C.pelts o4 = C.pelts q ∧ C.data o4 = C.data q ∧ C.min o4 = C.min q ∧ C.max o4 = C.max q ∧ C.zone1 o4 = C.zone1 q ∧ C.writable o4 = C.writable q → int'32_in_bounds (BitVec.toInt sy - (1 : ℤ)) ∧ (∀(o5 : BitVec 32), BitVec.toInt o5 = BitVec.toInt sy - (1 : ℤ) → (C.min y ≤ C.offset y + BitVec.toInt o5 ∧ C.offset y + BitVec.toInt o5 < C.max y) ∧ (let dh : BitVec 64 := C.pelts y (C.offset y + BitVec.toInt o5); int'32_in_bounds (BitVec.toInt sy - (2 : ℤ)) ∧ (∀(o6 : BitVec 32), BitVec.toInt o6 = BitVec.toInt sy - (2 : ℤ) → (C.min y ≤ C.offset y + BitVec.toInt o6 ∧ C.offset y + BitVec.toInt o6 < C.max y) ∧ (let dl : BitVec 64 := C.pelts y (C.offset y + BitVec.toInt o6); ((18446744073709551615 : ℤ) + (1 : ℤ)) / (2 : ℤ) ≤ BitVec.toUInt dh ∧ (∀(v : BitVec 64), reciprocal_3by2 v dh dl → int'32_in_bounds (BitVec.toInt sx - BitVec.toInt sy) ∧ (∀(o7 : BitVec 32), BitVec.toInt o7 = BitVec.toInt sx - BitVec.toInt sy → int'32_in_bounds ((2 : ℤ) - BitVec.toInt sy) ∧ (∀(mdn : BitVec 32), BitVec.toInt mdn = (2 : ℤ) - BitVec.toInt sy → (C.min o2 ≤ C.offset o2 + BitVec.toInt mdn ∧ C.offset o2 + BitVec.toInt mdn ≤ C.max o2) ∧ (∀(xd : C.ptr (BitVec 64)), C.offset xd = C.offset o2 + BitVec.toInt mdn ∧ C.plength xd = C.plength o2 ∧ C.pelts xd = C.pelts o2 ∧ C.data xd = C.data o2 ∧ C.min xd = C.min o2 ∧ C.max xd = C.max o2 ∧ C.zone1 xd = C.zone1 o2 ∧ C.writable xd = C.writable o2 → (let vy : ℤ := Lemmas.value y (BitVec.toInt sy); (C.valid xd (BitVec.toInt sy) ∧ C.valid y (BitVec.toInt sy)) ∧ (∀(r : BitVec 32), BitVec.toInt r = Compare.compare_int (Lemmas.value xd (BitVec.toInt sy)) (Lemmas.value y (BitVec.toInt sy)) → (∀(qh : BitVec 64), (if (0 : ℤ) ≤ BitVec.toInt r then qh = (1 : BitVec 64) else qh = (0 : BitVec 64)) → (∀(o8 : Bool), (BitVec.toUInt qh = BitVec.toUInt (0 : BitVec 64) → o8 = true) ∧ (o8 = true → qh = (0 : BitVec 64)) → ¬o8 = true → (0 : ℤ) ≤ BitVec.toInt sy ∧ C.valid xd (BitVec.toInt sy) ∧ C.valid y (BitVec.toInt sy) ∧ C.writable xd = true) ∧ (∀(x1 : C.ptr (BitVec 64)) (xp : C.ptr (BitVec 64)), (∃(o8 : Bool), ((BitVec.toUInt qh = BitVec.toUInt (0 : BitVec 64) → o8 = true) ∧ (o8 = true → qh = (0 : BitVec 64))) ∧ (if ¬o8 = true then ∃(xd1 : C.ptr (BitVec 64)), ((C.data xd1 = C.data x1 ∧ List.length (C.data x1) = List.length (C.data xd) ∧ C.offset xd1 = C.offset xd ∧ C.min xd1 = C.min xd ∧ C.max xd1 = C.max xd ∧ C.writable xd1 = C.writable xd ∧ C.zone1 xd1 = C.zone1 xd) ∧ (C.data xp = C.data x1 ∧ List.length (C.data x1) = List.length (C.data o2) ∧ C.offset xp = C.offset o2 ∧ C.min xp = C.min o2 ∧ C.max xp = C.max o2 ∧ C.writable xp = C.writable o2 ∧ C.zone1 xp = C.zone1 o2) ∧ List.length (C.data x1) = List.length (C.data x) ∧ C.offset x1 = C.offset x ∧ C.min x1 = C.min x ∧ C.max x1 = C.max x ∧ C.writable x1 = C.writable x ∧ C.zone1 x1 = C.zone1 x) ∧ (∃(b : BitVec 64), Lemmas.value xd1 (BitVec.toInt sy) - HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy)) * BitVec.toUInt b = Lemmas.value xd (BitVec.toInt sy) - Lemmas.value y (BitVec.toInt sy) ∧ ((0 : ℤ) ≤ BitVec.toUInt b ∧ BitVec.toUInt b ≤ (1 : ℤ)) ∧ (∀(j : ℤ), j < C.offset xd1 ∨ C.offset xd1 + BitVec.toInt sy ≤ j → C.pelts xd1 j = C.pelts xd j)) else x1 = x ∧ xp = o2)) → (C.min xp ≤ C.offset xp + (1 : ℤ) ∧ C.offset xp + (1 : ℤ) < C.max xp) ∧ (C.min xp ≤ C.offset xp + (1 : ℤ) ∧ C.offset xp + (1 : ℤ) < C.max xp) ∧ (((0 : ℤ) ≤ BitVec.toInt o7 ∧ BitVec.toInt o7 ≤ BitVec.toInt sx - BitVec.toInt sy) ∧ C.offset o4 = C.offset q + BitVec.toInt o7 ∧ C.offset xp = C.offset x1 + BitVec.toInt sy + BitVec.toInt o7 - (2 : ℤ) ∧ C.plength o4 = C.plength q ∧ C.min o4 = C.min q ∧ C.max o4 = C.max q ∧ C.plength xp = C.plength x1 ∧ C.min xp = C.min x1 ∧ C.max xp = C.max x1 ∧ C.pelts o4 = C.pelts q ∧ C.pelts xp = C.pelts x1 ∧ (C.writable o4 = true ∧ C.writable xp = true) ∧ Lemmas.value x (BitVec.toInt sx) = (Lemmas.value o4 (BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o7) + BitVec.toUInt qh * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o7))) * vy * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt o7)) + Lemmas.value x1 (BitVec.toInt sy + BitVec.toInt o7 - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy + BitVec.toInt o7 - (1 : ℤ))) * BitVec.toUInt (C.pelts xp (C.offset xp + (1 : ℤ))) ∧ Lemmas.value_sub (C.pelts x1) (C.offset xp + BitVec.toInt mdn) (C.offset xp + BitVec.toInt mdn + BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt (C.pelts xp (C.offset xp + (1 : ℤ))) < vy ∧ BitVec.toUInt (C.pelts x1 (C.offset xp)) + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt (C.pelts xp (C.offset xp + (1 : ℤ))) ≤ BitVec.toUInt dl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt dh) ∧ (∀(x11 : BitVec 64) (i : BitVec 32) (qp : C.ptr (BitVec 64)) (xp1 : C.ptr (BitVec 64)) (x2 : C.ptr (BitVec 64)) (q1 : C.ptr (BitVec 64)), List.length (C.data x2) = List.length (C.data x1) ∧ C.offset x2 = C.offset x1 ∧ C.min x2 = C.min x1 ∧ C.max x2 = C.max x1 ∧ C.writable x2 = C.writable x1 ∧ C.zone1 x2 = C.zone1 x1 → List.length (C.data q1) = List.length (C.data q) ∧ C.offset q1 = C.offset q ∧ C.min q1 = C.min q ∧ C.max q1 = C.max q ∧ C.writable q1 = C.writable q ∧ C.zone1 q1 = C.zone1 q → ((0 : ℤ) ≤ BitVec.toInt i ∧ BitVec.toInt i ≤ BitVec.toInt sx - BitVec.toInt sy) ∧ C.offset qp = C.offset q1 + BitVec.toInt i ∧ C.offset xp1 = C.offset x2 + BitVec.toInt sy + BitVec.toInt i - (2 : ℤ) ∧ C.plength qp = C.plength q1 ∧ C.min qp = C.min q1 ∧ C.max qp = C.max q1 ∧ C.plength xp1 = C.plength x2 ∧ C.min xp1 = C.min x2 ∧ C.max xp1 = C.max x2 ∧ C.pelts qp = C.pelts q1 ∧ C.pelts xp1 = C.pelts x2 ∧ (C.writable qp = true ∧ C.writable xp1 = true) ∧ Lemmas.value x (BitVec.toInt sx) = (Lemmas.value qp (BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt i) + BitVec.toUInt qh * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt i))) * vy * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt i)) + Lemmas.value x2 (BitVec.toInt sy + BitVec.toInt i - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy + BitVec.toInt i - (1 : ℤ))) * BitVec.toUInt x11 ∧ Lemmas.value_sub (C.pelts x2) (C.offset xp1 + BitVec.toInt mdn) (C.offset xp1 + BitVec.toInt mdn + BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt x11 < vy ∧ BitVec.toUInt (C.pelts x2 (C.offset xp1)) + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt x11 ≤ BitVec.toUInt dl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt dh → (if (0 : ℤ) < BitVec.toInt i then int'32_in_bounds (BitVec.toInt i - (1 : ℤ)) ∧ (∀(o8 : BitVec 32), BitVec.toInt o8 = BitVec.toInt i - (1 : ℤ) → (C.min xp1 ≤ C.offset xp1 + -(1 : ℤ) ∧ C.offset xp1 + -(1 : ℤ) ≤ C.max xp1) ∧ (∀(o9 : C.ptr (BitVec 64)), C.offset o9 = C.offset xp1 + -(1 : ℤ) ∧ C.plength o9 = C.plength xp1 ∧ C.pelts o9 = C.pelts xp1 ∧ C.data o9 = C.data xp1 ∧ C.min o9 = C.min xp1 ∧ C.max o9 = C.max xp1 ∧ C.zone1 o9 = C.zone1 xp1 ∧ C.writable o9 = C.writable xp1 → (C.min o9 ≤ C.offset o9 + BitVec.toInt mdn ∧ C.offset o9 + BitVec.toInt mdn ≤ C.max o9) ∧ (∀(xd1 : C.ptr (BitVec 64)), C.offset xd1 = C.offset o9 + BitVec.toInt mdn ∧ C.plength xd1 = C.plength o9 ∧ C.pelts xd1 = C.pelts o9 ∧ C.data xd1 = C.data o9 ∧ C.min xd1 = C.min o9 ∧ C.max xd1 = C.max o9 ∧ C.zone1 xd1 = C.zone1 o9 ∧ C.writable xd1 = C.writable o9 → (C.min o9 ≤ C.offset o9 + (1 : ℤ) ∧ C.offset o9 + (1 : ℤ) < C.max o9) ∧ (let nx0 : BitVec 64 := C.pelts o9 (C.offset o9 + (1 : ℤ)); ∀(o10 : Bool), (BitVec.toUInt x11 = BitVec.toUInt dh → o10 = true) ∧ (o10 = true → x11 = dh) → (∀(o11 : Bool), (if o10 = true then (BitVec.toUInt nx0 = BitVec.toUInt dl → o11 = true) ∧ (o11 = true → nx0 = dl) else o11 = false) → (if o11 = true then Lemmas.value_sub (C.pelts xd1) (C.offset xd1 + (1 : ℤ)) (C.offset xd1 + BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (2 : ℤ))) * BitVec.toUInt dl + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt dh < vy ∧ (Lemmas.value_sub (C.pelts xd1) (C.offset xd1 + (1 : ℤ)) (C.offset xd1 + BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (2 : ℤ))) * BitVec.toUInt dl + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt dh < vy → (let o12 : List (BitVec 64) := C.data x2; ∀(xc : List (BitVec 64)), List.length xc = List.length o12 ∧ (∀(i1 : ℤ), (0 : ℤ) ≤ i1 ∧ i1 < Int.ofNat (List.length xc) → xc[Int.toNat i1]! = o12[Int.toNat i1]!) → (C.valid y (BitVec.toInt sy) ∧ C.valid xd1 (BitVec.toInt sy) ∧ C.writable xd1 = true) ∧ (∀(xd2 : C.ptr (BitVec 64)) (xp2 : C.ptr (BitVec 64)) (x3 : C.ptr (BitVec 64)), C.data xd2 = C.data x3 ∧ List.length (C.data x3) = List.length (C.data xd1) ∧ C.offset xd2 = C.offset xd1 ∧ C.min xd2 = C.min xd1 ∧ C.max xd2 = C.max xd1 ∧ C.writable xd2 = C.writable xd1 ∧ C.zone1 xd2 = C.zone1 xd1 → C.data xp2 = C.data x3 ∧ List.length (C.data x3) = List.length (C.data o9) ∧ C.offset xp2 = C.offset o9 ∧ C.min xp2 = C.min o9 ∧ C.max xp2 = C.max o9 ∧ C.writable xp2 = C.writable o9 ∧ C.zone1 xp2 = C.zone1 o9 → List.length (C.data x3) = List.length (C.data x2) ∧ C.offset x3 = C.offset x2 ∧ C.min x3 = C.min x2 ∧ C.max x3 = C.max x2 ∧ C.writable x3 = C.writable x2 ∧ C.zone1 x3 = C.zone1 x2 → (∀(b : BitVec 64), Lemmas.value xd2 (BitVec.toInt sy) - HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy)) * BitVec.toUInt b = Lemmas.value xd1 (BitVec.toInt sy) - Lemmas.value y (BitVec.toInt sy) * BitVec.toUInt uint'64_max ∧ (∀(j : ℤ), j < C.offset xd2 ∨ C.offset xd2 + BitVec.toInt sy ≤ j → C.pelts xd2 j = C.pelts xd1 j) → Lemmas.value x3 (BitVec.toInt o8) = Lemmas.value x2 (BitVec.toInt o8) ∧ (Lemmas.value x3 (BitVec.toInt o8) = Lemmas.value x2 (BitVec.toInt o8) → (let o13 : ℤ := C.offset x3 + (BitVec.toInt sy + BitVec.toInt o8 - (1 : ℤ)); let o14 : ℤ := C.offset xd2; let o15 : ℤ := C.offset x3; let o16 : ℤ -> BitVec 64 := C.pelts x3; (o15 ≤ o14 ∧ o14 ≤ o13) ∧ (Lemmas.value_sub o16 o15 o13 = Lemmas.value_sub o16 o15 o14 + Lemmas.value_sub o16 o14 o13 * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (o14 - o15)) → (C.min xp2 ≤ C.offset xp2 + (1 : ℤ) ∧ C.offset xp2 + (1 : ℤ) < C.max xp2) ∧ (C.min qp ≤ C.offset qp + -(1 : ℤ) ∧ C.offset qp + -(1 : ℤ) ≤ C.max qp) ∧ (∀(o17 : C.ptr (BitVec 64)), C.offset o17 = C.offset qp + -(1 : ℤ) ∧ C.plength o17 = C.plength qp ∧ C.pelts o17 = C.pelts qp ∧ C.data o17 = C.data qp ∧ C.min o17 = C.min qp ∧ C.max o17 = C.max qp ∧ C.zone1 o17 = C.zone1 qp ∧ C.writable o17 = C.writable qp → (let o18 : ℤ := C.offset o17 + BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o8; let o19 : ℤ := C.offset o17 + (1 : ℤ); let o20 : ℤ := C.offset o17; let o21 : ℤ -> BitVec 64 := C.pelts q1; (o19 ≤ o18 ∧ (o20 < o19 ∨ o18 ≤ o20)) ∧ (Lemmas.value_sub o21 o19 o18 = Lemmas.value_sub (Function.update o21 o20 uint'64_max) o19 o18 → ((C.min o17 ≤ C.offset o17 ∧ C.offset o17 < C.max o17) ∧ C.writable o17 = true) ∧ (∀(qp1 : C.ptr (BitVec 64)) (q2 : C.ptr (BitVec 64)), C.data qp1 = C.data q2 ∧ List.length (C.data q2) = List.length (C.data o17) ∧ C.offset qp1 = C.offset o17 ∧ C.min qp1 = C.min o17 ∧ C.max qp1 = C.max o17 ∧ C.writable qp1 = C.writable o17 ∧ C.zone1 qp1 = C.zone1 o17 → C.data qp1 = C.data q2 ∧ List.length (C.data q2) = List.length (C.data o17) ∧ C.offset qp1 = C.offset o17 ∧ C.min qp1 = C.min o17 ∧ C.max qp1 = C.max o17 ∧ C.writable qp1 = C.writable o17 ∧ C.zone1 qp1 = C.zone1 o17 → List.length (C.data q2) = List.length (C.data q1) ∧ C.offset q2 = C.offset q1 ∧ C.min q2 = C.min q1 ∧ C.max q2 = C.max q1 ∧ C.writable q2 = C.writable q1 ∧ C.zone1 q2 = C.zone1 q1 → C.pelts qp1 = Function.update (C.pelts o17) (C.offset qp1) uint'64_max → BitVec.toInt o8 < BitVec.toInt i ∧ ((0 : ℤ) ≤ BitVec.toInt o8 ∧ BitVec.toInt o8 ≤ BitVec.toInt sx - BitVec.toInt sy) ∧ C.offset qp1 = C.offset q2 + BitVec.toInt o8 ∧ C.offset xp2 = C.offset x3 + BitVec.toInt sy + BitVec.toInt o8 - (2 : ℤ) ∧ C.plength qp1 = C.plength q2 ∧ C.min qp1 = C.min q2 ∧ C.max qp1 = C.max q2 ∧ C.plength xp2 = C.plength x3 ∧ C.min xp2 = C.min x3 ∧ C.max xp2 = C.max x3 ∧ C.pelts qp1 = C.pelts q2 ∧ C.pelts xp2 = C.pelts x3 ∧ (C.writable qp1 = true ∧ C.writable xp2 = true) ∧ Lemmas.value x (BitVec.toInt sx) = (Lemmas.value qp1 (BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o8) + BitVec.toUInt qh * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o8))) * vy * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt o8)) + Lemmas.value x3 (BitVec.toInt sy + BitVec.toInt o8 - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy + BitVec.toInt o8 - (1 : ℤ))) * BitVec.toUInt (C.pelts xp2 (C.offset xp2 + (1 : ℤ))) ∧ Lemmas.value_sub (C.pelts x3) (C.offset xp2 + BitVec.toInt mdn) (C.offset xp2 + BitVec.toInt mdn + BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt (C.pelts xp2 (C.offset xp2 + (1 : ℤ))) < vy ∧ BitVec.toUInt (C.pelts x3 (C.offset xp2)) + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt (C.pelts xp2 (C.offset xp2 + (1 : ℤ))) ≤ BitVec.toUInt dl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt dh))))))))))) else let vlx : ℤ := Lemmas.value xd1 (BitVec.toInt sy - (2 : ℤ)); (C.min o9 ≤ C.offset o9 ∧ C.offset o9 < C.max o9) ∧ (let xp0 : BitVec 64 := C.pelts o9 (C.offset o9); (C.min o9 ≤ C.offset o9 + (1 : ℤ) ∧ C.offset o9 + (1 : ℤ) < C.max o9) ∧ (let xp11 : BitVec 64 := C.pelts o9 (C.offset o9 + (1 : ℤ)); Lemmas.value xd1 (BitVec.toInt sy) = vlx + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (2 : ℤ))) * (BitVec.toUInt xp0 + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt xp11) ∧ (Lemmas.value xd1 (BitVec.toInt sy) = vlx + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (2 : ℤ))) * (BitVec.toUInt xp0 + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt xp11) → (((18446744073709551615 : ℤ) + (1 : ℤ)) / (2 : ℤ) ≤ BitVec.toUInt dh ∧ reciprocal_3by2 v dh dl ∧ BitVec.toUInt xp11 + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt x11 < BitVec.toUInt dl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt dh) ∧ (∀(qu : BitVec 64) (rl : BitVec 64) (rh : BitVec 64), BitVec.toUInt qu * BitVec.toUInt dl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt qu * BitVec.toUInt dh + BitVec.toUInt rl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt rh = BitVec.toUInt xp0 + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt xp11 + ((18446744073709551615 : ℤ) + (1 : ℤ)) * ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt x11 ∧ (0 : ℤ) ≤ BitVec.toUInt rl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt rh ∧ BitVec.toUInt rl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt rh < BitVec.toUInt dl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt dh → (let o12 : ℤ := C.offset x2 + BitVec.toInt sy + BitVec.toInt i - (1 : ℤ); let o13 : ℤ := C.offset xd1; let o14 : ℤ := C.offset x2; let o15 : ℤ -> BitVec 64 := C.pelts x2; (o14 ≤ o13 ∧ o13 ≤ o12) ∧ (Lemmas.value_sub o15 o14 o12 = Lemmas.value_sub o15 o14 o13 + Lemmas.value_sub o15 o13 o12 * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (o13 - o14)) → (let o16 : List (BitVec 64) := C.data x2; ∀(xc : List (BitVec 64)), List.length xc = List.length o16 ∧ (∀(i1 : ℤ), (0 : ℤ) ≤ i1 ∧ i1 < Int.ofNat (List.length xc) → xc[Int.toNat i1]! = o16[Int.toNat i1]!) → int'32_in_bounds (BitVec.toInt sy - (2 : ℤ)) ∧ (∀(o17 : BitVec 32), BitVec.toInt o17 = BitVec.toInt sy - (2 : ℤ) → (C.valid y (BitVec.toInt o17) ∧ C.valid xd1 (BitVec.toInt o17) ∧ C.writable xd1 = true) ∧ (∀(xd2 : C.ptr (BitVec 64)) (xp2 : C.ptr (BitVec 64)) (x3 : C.ptr (BitVec 64)), C.data xd2 = C.data x3 ∧ List.length (C.data x3) = List.length (C.data xd1) ∧ C.offset xd2 = C.offset xd1 ∧ C.min xd2 = C.min xd1 ∧ C.max xd2 = C.max xd1 ∧ C.writable xd2 = C.writable xd1 ∧ C.zone1 xd2 = C.zone1 xd1 → C.data xp2 = C.data x3 ∧ List.length (C.data x3) = List.length (C.data o9) ∧ C.offset xp2 = C.offset o9 ∧ C.min xp2 = C.min o9 ∧ C.max xp2 = C.max o9 ∧ C.writable xp2 = C.writable o9 ∧ C.zone1 xp2 = C.zone1 o9 → List.length (C.data x3) = List.length (C.data x2) ∧ C.offset x3 = C.offset x2 ∧ C.min x3 = C.min x2 ∧ C.max x3 = C.max x2 ∧ C.writable x3 = C.writable x2 ∧ C.zone1 x3 = C.zone1 x2 → (∀(cy : BitVec 64), Lemmas.value xd2 (BitVec.toInt o17) - HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt o17)) * BitVec.toUInt cy = Lemmas.value xd1 (BitVec.toInt o17) - Lemmas.value y (BitVec.toInt o17) * BitVec.toUInt qu ∧ (∀(j : ℤ), j < C.offset xd2 ∨ C.offset xd2 + BitVec.toInt o17 ≤ j → C.pelts xd2 j = C.pelts xd1 j) → Lemmas.value x3 (BitVec.toInt o8) = Lemmas.value x2 (BitVec.toInt o8) ∧ (Lemmas.value x3 (BitVec.toInt o8) = Lemmas.value x2 (BitVec.toInt o8) → (∀(cy1 : BitVec 64), (if BitVec.toUInt rl < BitVec.toUInt cy then cy1 = (1 : BitVec 64) else cy1 = (0 : BitVec 64)) → (∀(o18 : BitVec 64), BitVec.toUInt o18 = (BitVec.toUInt rl - BitVec.toUInt cy) % ((18446744073709551615 : ℤ) + (1 : ℤ)) → (∀(cy2 : BitVec 64), (if BitVec.toUInt rh < BitVec.toUInt cy1 then cy2 = (1 : BitVec 64) else cy2 = (0 : BitVec 64)) → (∀(o19 : BitVec 64), BitVec.toUInt o19 = (BitVec.toUInt rh - BitVec.toUInt cy1) % ((18446744073709551615 : ℤ) + (1 : ℤ)) → (let o20 : ℤ := C.offset xd2 + BitVec.toInt sy - (1 : ℤ); let o21 : ℤ := C.offset xd2; let o22 : ℤ := C.offset xp2; let o23 : ℤ -> BitVec 64 := C.pelts x3; (o21 ≤ o22 ∧ o22 < o20) ∧ (Lemmas.value_sub (Function.update o23 o22 o18) o21 o20 = Lemmas.value_sub o23 o21 o20 + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (o22 - o21)) * (BitVec.toUInt o18 - BitVec.toUInt (o23 o22)) → (let o24 : ℤ := C.offset x3 + BitVec.toInt o8; let o25 : ℤ := C.offset x3; let o26 : ℤ := C.offset xp2; let o27 : ℤ -> BitVec 64 := C.pelts x3; (o25 ≤ o24 ∧ (o26 < o25 ∨ o24 ≤ o26)) ∧ (Lemmas.value_sub o27 o25 o24 = Lemmas.value_sub (Function.update o27 o26 o18) o25 o24 → (let o28 : ℤ := C.offset xd2 + BitVec.toInt sy - (2 : ℤ); let o29 : ℤ := C.offset xd2; let o30 : ℤ := C.offset xp2; let o31 : ℤ -> BitVec 64 := C.pelts x3; (o29 ≤ o28 ∧ (o30 < o29 ∨ o28 ≤ o30)) ∧ (Lemmas.value_sub o31 o29 o28 = Lemmas.value_sub (Function.update o31 o30 o18) o29 o28 → ((C.min xp2 ≤ C.offset xp2 ∧ C.offset xp2 < C.max xp2) ∧ C.writable xp2 = true) ∧ (∀(xd3 : C.ptr (BitVec 64)) (xp3 : C.ptr (BitVec 64)) (x4 : C.ptr (BitVec 64)), C.data xp3 = C.data x4 ∧ List.length (C.data x4) = List.length (C.data xp2) ∧ C.offset xp3 = C.offset xp2 ∧ C.min xp3 = C.min xp2 ∧ C.max xp3 = C.max xp2 ∧ C.writable xp3 = C.writable xp2 ∧ C.zone1 xp3 = C.zone1 xp2 → C.data xd3 = C.data x4 ∧ List.length (C.data x4) = List.length (C.data xd2) ∧ C.offset xd3 = C.offset xd2 ∧ C.min xd3 = C.min xd2 ∧ C.max xd3 = C.max xd2 ∧ C.writable xd3 = C.writable xd2 ∧ C.zone1 xd3 = C.zone1 xd2 → C.data xp3 = C.data x4 ∧ List.length (C.data x4) = List.length (C.data xp2) ∧ C.offset xp3 = C.offset xp2 ∧ C.min xp3 = C.min xp2 ∧ C.max xp3 = C.max xp2 ∧ C.writable xp3 = C.writable xp2 ∧ C.zone1 xp3 = C.zone1 xp2 → List.length (C.data x4) = List.length (C.data x3) ∧ C.offset x4 = C.offset x3 ∧ C.min x4 = C.min x3 ∧ C.max x4 = C.max x3 ∧ C.writable x4 = C.writable x3 ∧ C.zone1 x4 = C.zone1 x3 → C.pelts xp3 = Function.update (C.pelts xp2) (C.offset xp3) o18 → Lemmas.value xd3 (BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt o19 - HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy)) * BitVec.toUInt cy2 = Lemmas.value xd1 (BitVec.toInt sy) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy)) * BitVec.toUInt x11 - BitVec.toUInt qu * vy ∧ (Lemmas.value xd3 (BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt o19 - HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy)) * BitVec.toUInt cy2 = Lemmas.value xd1 (BitVec.toInt sy) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy)) * BitVec.toUInt x11 - BitVec.toUInt qu * vy → (∀(o32 : Bool), (BitVec.toUInt cy2 = BitVec.toUInt (0 : BitVec 64) → o32 = true) ∧ (o32 = true → cy2 = (0 : BitVec 64)) → (if ¬o32 = true then (0 : ℤ) < BitVec.toUInt qu ∧ ((0 : ℤ) < BitVec.toUInt qu → HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy)) - vy ≤ Lemmas.value xd3 (BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt o19 ∧ (HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy)) - vy ≤ Lemmas.value xd3 (BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt o19 → (let o33 : List (BitVec 64) := C.data x4; ∀(xc1 : List (BitVec 64)), List.length xc1 = List.length o33 ∧ (∀(i1 : ℤ), (0 : ℤ) ≤ i1 ∧ i1 < Int.ofNat (List.length xc1) → xc1[Int.toNat i1]! = o33[Int.toNat i1]!) → int'32_in_bounds (BitVec.toInt sy - (1 : ℤ)) ∧ (∀(o34 : BitVec 32), BitVec.toInt o34 = BitVec.toInt sy - (1 : ℤ) → (C.valid xd3 (BitVec.toInt o34) ∧ C.valid y (BitVec.toInt o34) ∧ C.writable xd3 = true) ∧ (∀(xd4 : C.ptr (BitVec 64)) (xp4 : C.ptr (BitVec 64)) (x5 : C.ptr (BitVec 64)), C.data xd4 = C.data x5 ∧ List.length (C.data x5) = List.length (C.data xd3) ∧ C.offset xd4 = C.offset xd3 ∧ C.min xd4 = C.min xd3 ∧ C.max xd4 = C.max xd3 ∧ C.writable xd4 = C.writable xd3 ∧ C.zone1 xd4 = C.zone1 xd3 → C.data xp4 = C.data x5 ∧ List.length (C.data x5) = List.length (C.data xp3) ∧ C.offset xp4 = C.offset xp3 ∧ C.min xp4 = C.min xp3 ∧ C.max xp4 = C.max xp3 ∧ C.writable xp4 = C.writable xp3 ∧ C.zone1 xp4 = C.zone1 xp3 → List.length (C.data x5) = List.length (C.data x4) ∧ C.offset x5 = C.offset x4 ∧ C.min x5 = C.min x4 ∧ C.max x5 = C.max x4 ∧ C.writable x5 = C.writable x4 ∧ C.zone1 x5 = C.zone1 x4 → (∀(c : BitVec 64), ((0 : ℤ) ≤ BitVec.toUInt c ∧ BitVec.toUInt c ≤ (1 : ℤ)) ∧ Lemmas.value xd4 (BitVec.toInt o34) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt o34)) * BitVec.toUInt c = Lemmas.value xd3 (BitVec.toInt o34) + Lemmas.value y (BitVec.toInt o34) ∧ (∀(j : ℤ), j < C.offset xd4 ∨ C.offset xd4 + BitVec.toInt o34 ≤ j → C.pelts xd4 j = C.pelts xd3 j) → Lemmas.value x5 (BitVec.toInt o8) = Lemmas.value x4 (BitVec.toInt o8) ∧ (Lemmas.value x5 (BitVec.toInt o8) = Lemmas.value x4 (BitVec.toInt o8) → (¬(18446744073709551615 : ℤ) + (1 : ℤ) = (0 : ℤ) ∧ (∀(o35 : BitVec 64), BitVec.toUInt o35 = (BitVec.toUInt dh + BitVec.toUInt c) % ((18446744073709551615 : ℤ) + (1 : ℤ)) → (∀(o36 : BitVec 64), BitVec.toUInt o36 = (BitVec.toUInt o19 + BitVec.toUInt o35) % ((18446744073709551615 : ℤ) + (1 : ℤ)) → Lemmas.value xd4 (BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt o36 = Lemmas.value xd3 (BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt o19 + vy - HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy))))) ∧ (∀(x12 : BitVec 64), Lemmas.value xd4 (BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt x12 = Lemmas.value xd3 (BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt o19 + vy - HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy)) → uint'64_in_bounds (BitVec.toUInt qu - (1 : ℤ)) ∧ (∀(o35 : BitVec 64), BitVec.toUInt o35 = BitVec.toUInt qu - (1 : ℤ) → (C.min qp ≤ C.offset qp + -(1 : ℤ) ∧ C.offset qp + -(1 : ℤ) ≤ C.max qp) ∧ (∀(o36 : C.ptr (BitVec 64)), C.offset o36 = C.offset qp + -(1 : ℤ) ∧ C.plength o36 = C.plength qp ∧ C.pelts o36 = C.pelts qp ∧ C.data o36 = C.data qp ∧ C.min o36 = C.min qp ∧ C.max o36 = C.max qp ∧ C.zone1 o36 = C.zone1 qp ∧ C.writable o36 = C.writable qp → (let o37 : ℤ := C.offset o36 + BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o8; let o38 : ℤ := C.offset o36 + (1 : ℤ); let o39 : ℤ := C.offset o36; let o40 : ℤ -> BitVec 64 := C.pelts q1; (o38 ≤ o37 ∧ (o39 < o38 ∨ o37 ≤ o39)) ∧ (Lemmas.value_sub o40 o38 o37 = Lemmas.value_sub (Function.update o40 o39 o35) o38 o37 → ((C.min o36 ≤ C.offset o36 ∧ C.offset o36 < C.max o36) ∧ C.writable o36 = true) ∧ (∀(qp1 : C.ptr (BitVec 64)) (q2 : C.ptr (BitVec 64)), C.data qp1 = C.data q2 ∧ List.length (C.data q2) = List.length (C.data o36) ∧ C.offset qp1 = C.offset o36 ∧ C.min qp1 = C.min o36 ∧ C.max qp1 = C.max o36 ∧ C.writable qp1 = C.writable o36 ∧ C.zone1 qp1 = C.zone1 o36 → C.data qp1 = C.data q2 ∧ List.length (C.data q2) = List.length (C.data o36) ∧ C.offset qp1 = C.offset o36 ∧ C.min qp1 = C.min o36 ∧ C.max qp1 = C.max o36 ∧ C.writable qp1 = C.writable o36 ∧ C.zone1 qp1 = C.zone1 o36 → List.length (C.data q2) = List.length (C.data q1) ∧ C.offset q2 = C.offset q1 ∧ C.min q2 = C.min q1 ∧ C.max q2 = C.max q1 ∧ C.writable q2 = C.writable q1 ∧ C.zone1 q2 = C.zone1 q1 → C.pelts qp1 = Function.update (C.pelts o36) (C.offset qp1) o35 → BitVec.toInt o8 < BitVec.toInt i ∧ ((0 : ℤ) ≤ BitVec.toInt o8 ∧ BitVec.toInt o8 ≤ BitVec.toInt sx - BitVec.toInt sy) ∧ C.offset qp1 = C.offset q2 + BitVec.toInt o8 ∧ C.offset xp4 = C.offset x5 + BitVec.toInt sy + BitVec.toInt o8 - (2 : ℤ) ∧ C.plength qp1 = C.plength q2 ∧ C.min qp1 = C.min q2 ∧ C.max qp1 = C.max q2 ∧ C.plength xp4 = C.plength x5 ∧ C.min xp4 = C.min x5 ∧ C.max xp4 = C.max x5 ∧ C.pelts qp1 = C.pelts q2 ∧ C.pelts xp4 = C.pelts x5 ∧ (C.writable qp1 = true ∧ C.writable xp4 = true) ∧ Lemmas.value x (BitVec.toInt sx) = (Lemmas.value qp1 (BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o8) + BitVec.toUInt qh * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o8))) * vy * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt o8)) + Lemmas.value x5 (BitVec.toInt sy + BitVec.toInt o8 - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy + BitVec.toInt o8 - (1 : ℤ))) * BitVec.toUInt x12 ∧ Lemmas.value_sub (C.pelts x5) (C.offset xp4 + BitVec.toInt mdn) (C.offset xp4 + BitVec.toInt mdn + BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt x12 < vy ∧ BitVec.toUInt (C.pelts x5 (C.offset xp4)) + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt x12 ≤ BitVec.toUInt dl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt dh))))))))))))) else (C.min qp ≤ C.offset qp + -(1 : ℤ) ∧ C.offset qp + -(1 : ℤ) ≤ C.max qp) ∧ (∀(o33 : C.ptr (BitVec 64)), C.offset o33 = C.offset qp + -(1 : ℤ) ∧ C.plength o33 = C.plength qp ∧ C.pelts o33 = C.pelts qp ∧ C.data o33 = C.data qp ∧ C.min o33 = C.min qp ∧ C.max o33 = C.max qp ∧ C.zone1 o33 = C.zone1 qp ∧ C.writable o33 = C.writable qp → (let o34 : ℤ := C.offset o33 + BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o8; let o35 : ℤ := C.offset o33 + (1 : ℤ); let o36 : ℤ := C.offset o33; let o37 : ℤ -> BitVec 64 := C.pelts q1; (o35 ≤ o34 ∧ (o36 < o35 ∨ o34 ≤ o36)) ∧ (Lemmas.value_sub o37 o35 o34 = Lemmas.value_sub (Function.update o37 o36 qu) o35 o34 → ((C.min o33 ≤ C.offset o33 ∧ C.offset o33 < C.max o33) ∧ C.writable o33 = true) ∧ (∀(qp1 : C.ptr (BitVec 64)) (q2 : C.ptr (BitVec 64)), C.data qp1 = C.data q2 ∧ List.length (C.data q2) = List.length (C.data o33) ∧ C.offset qp1 = C.offset o33 ∧ C.min qp1 = C.min o33 ∧ C.max qp1 = C.max o33 ∧ C.writable qp1 = C.writable o33 ∧ C.zone1 qp1 = C.zone1 o33 → C.data qp1 = C.data q2 ∧ List.length (C.data q2) = List.length (C.data o33) ∧ C.offset qp1 = C.offset o33 ∧ C.min qp1 = C.min o33 ∧ C.max qp1 = C.max o33 ∧ C.writable qp1 = C.writable o33 ∧ C.zone1 qp1 = C.zone1 o33 → List.length (C.data q2) = List.length (C.data q1) ∧ C.offset q2 = C.offset q1 ∧ C.min q2 = C.min q1 ∧ C.max q2 = C.max q1 ∧ C.writable q2 = C.writable q1 ∧ C.zone1 q2 = C.zone1 q1 → C.pelts qp1 = Function.update (C.pelts o33) (C.offset qp1) qu → BitVec.toInt o8 < BitVec.toInt i ∧ ((0 : ℤ) ≤ BitVec.toInt o8 ∧ BitVec.toInt o8 ≤ BitVec.toInt sx - BitVec.toInt sy) ∧ C.offset qp1 = C.offset q2 + BitVec.toInt o8 ∧ C.offset xp3 = C.offset x4 + BitVec.toInt sy + BitVec.toInt o8 - (2 : ℤ) ∧ C.plength qp1 = C.plength q2 ∧ C.min qp1 = C.min q2 ∧ C.max qp1 = C.max q2 ∧ C.plength xp3 = C.plength x4 ∧ C.min xp3 = C.min x4 ∧ C.max xp3 = C.max x4 ∧ C.pelts qp1 = C.pelts q2 ∧ C.pelts xp3 = C.pelts x4 ∧ (C.writable qp1 = true ∧ C.writable xp3 = true) ∧ Lemmas.value x (BitVec.toInt sx) = (Lemmas.value qp1 (BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o8) + BitVec.toUInt qh * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sx - BitVec.toInt sy - BitVec.toInt o8))) * vy * HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt o8)) + Lemmas.value x4 (BitVec.toInt sy + BitVec.toInt o8 - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy + BitVec.toInt o8 - (1 : ℤ))) * BitVec.toUInt o19 ∧ Lemmas.value_sub (C.pelts x4) (C.offset xp3 + BitVec.toInt mdn) (C.offset xp3 + BitVec.toInt mdn + BitVec.toInt sy - (1 : ℤ)) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sy - (1 : ℤ))) * BitVec.toUInt o19 < vy ∧ BitVec.toUInt (C.pelts x4 (C.offset xp3)) + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt o19 ≤ BitVec.toUInt dl + ((18446744073709551615 : ℤ) + (1 : ℤ)) * BitVec.toUInt dh))))))))))))))))))))))))))))))))))) else let o8 : ℤ := C.offset xp1; let o9 : ℤ := C.offset x2; let o10 : ℤ := C.offset xp1 + (1 : ℤ); let o11 : ℤ -> BitVec 64 := C.pelts x2; (o9 ≤ o8 ∧ (o10 < o9 ∨ o8 ≤ o10)) ∧ (Lemmas.value_sub o11 o9 o8 = Lemmas.value_sub (Function.update o11 o10 x11) o9 o8 → ((C.min xp1 ≤ C.offset xp1 + (1 : ℤ) ∧ C.offset xp1 + (1 : ℤ) < C.max xp1) ∧ C.writable xp1 = true) ∧ (∀(o12 : C.ptr (BitVec 64)) (x3 : C.ptr (BitVec 64)), C.data o12 = C.data x3 ∧ List.length (C.data x3) = List.length (C.data xp1) ∧ C.offset o12 = C.offset xp1 ∧ C.min o12 = C.min xp1 ∧ C.max o12 = C.max xp1 ∧ C.writable o12 = C.writable xp1 ∧ C.zone1 o12 = C.zone1 xp1 → List.length (C.data x3) = List.length (C.data x2) ∧ C.offset x3 = C.offset x2 ∧ C.min x3 = C.min x2 ∧ C.max x3 = C.max x2 ∧ C.writable x3 = C.writable x2 ∧ C.zone1 x3 = C.zone1 x2 → C.pelts o12 = Function.update (C.pelts xp1) (C.offset o12 + (1 : ℤ)) x11 ∧ C.pelts o12 (C.offset o12 + (1 : ℤ)) = x11 → Lemmas.value x (BitVec.toInt sx) = (Lemmas.value q1 (BitVec.toInt sx - BitVec.toInt sy) + HPow.hPow ((18446744073709551615 : ℤ) + (1 : ℤ)) (Int.toNat (BitVec.toInt sx - BitVec.toInt sy)) * BitVec.toUInt qh) * Lemmas.value y (BitVec.toInt sy) + Lemmas.value x3 (BitVec.toInt sy) ∧ Lemmas.value x3 (BitVec.toInt sy) < Lemmas.value y (BitVec.toInt sy) ∧ (0 : ℤ) ≤ BitVec.toUInt qh ∧ BitVec.toUInt qh ≤ (1 : ℤ)))))))))))))))))))))
  := sorry
end div_Div_div_sb_qrqtvc
