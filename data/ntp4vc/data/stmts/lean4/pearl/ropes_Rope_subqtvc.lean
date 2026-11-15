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

namespace MyString
axiom char : Type
axiom inhabited_axiom_char : Inhabited char
attribute [instance] inhabited_axiom_char
axiom dummy_char : char
axiom char_string : Type
axiom inhabited_axiom_char_string : Inhabited char_string
attribute [instance] inhabited_axiom_char_string
axiom length : char_string -> ℤ
axiom length'spec (x : char_string) : (0 : ℤ) ≤ length x
axiom mixfix_lbrb : char_string -> ℤ -> char
axiom empty : char_string
axiom empty'def : length empty = (0 : ℤ)
noncomputable def infix_eqeq (s1 : char_string) (s2 : char_string) := length s1 = length s2 ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < length s1 → mixfix_lbrb s1 i = mixfix_lbrb s2 i)
axiom extensionality (s1 : char_string) (s2 : char_string) (fact0 : infix_eqeq s1 s2) : s1 = s2
axiom app : char_string -> char_string -> char_string
axiom app_def1 (s1 : char_string) (s2 : char_string) : length (app s1 s2) = length s1 + length s2
axiom app_def2 (i : ℤ) (s1 : char_string) (s2 : char_string) (fact0 : (0 : ℤ) ≤ i) (fact1 : i < length s1) : mixfix_lbrb (app s1 s2) i = mixfix_lbrb s1 i
axiom app_def3 (s1 : char_string) (i : ℤ) (s2 : char_string) (fact0 : length s1 ≤ i) (fact1 : i < length s1 + length s2) : mixfix_lbrb (app s1 s2) i = mixfix_lbrb s2 (i - length s1)
axiom sub : char_string -> ℤ -> ℤ -> char_string
axiom sub_def1 (len : ℤ) (ofs : ℤ) (s : char_string) (fact0 : (0 : ℤ) ≤ len) (fact1 : (0 : ℤ) ≤ ofs) (fact2 : ofs ≤ length s) (fact3 : ofs + len ≤ length s) : length (sub s ofs len) = len
axiom sub_def2 (len : ℤ) (ofs : ℤ) (s : char_string) (i : ℤ) (fact0 : (0 : ℤ) ≤ len) (fact1 : (0 : ℤ) ≤ ofs) (fact2 : ofs ≤ length s) (fact3 : ofs + len ≤ length s) (fact4 : (0 : ℤ) ≤ i) (fact5 : i < len) : mixfix_lbrb (sub s ofs len) i = mixfix_lbrb s (ofs + i)
end MyString
namespace ropes_Rope_subqtvc
inductive rope where
  | Emp : rope
  | Str : MyString.char_string -> ℤ -> ℤ -> rope
  | App : rope -> rope -> ℤ -> rope
axiom inhabited_axiom_rope : Inhabited rope
attribute [instance] inhabited_axiom_rope
noncomputable def length (r : rope) := match r with | rope.Emp => (0 : ℤ) | rope.Str _ _ len => len | rope.App _ _ len => len
noncomputable def inv : rope -> Prop
  | rope.Emp => True
  | (rope.Str s ofs len) => (0 : ℤ) < len ∧ ((0 : ℤ) ≤ ofs ∧ ofs < MyString.length s) ∧ ofs + len ≤ MyString.length s
  | (rope.App l r1 len) => (0 : ℤ) < length l ∧ inv l ∧ (0 : ℤ) < length r1 ∧ inv r1 ∧ len = length l + length r1
noncomputable def string : rope -> MyString.char_string
  | rope.Emp => MyString.empty
  | (rope.Str s ofs len) => MyString.sub s ofs len
  | (rope.App l r1 x) => MyString.app (string l) (string r1)
axiom empty : rope
axiom empty'def : length empty = (0 : ℤ) ∧ inv empty ∧ MyString.infix_eqeq (string empty) MyString.empty
theorem sub'vc (r : rope) (len : ℤ) (ofs : ℤ) (fact0 : inv r) (fact1 : (0 : ℤ) ≤ len) (fact2 : (0 : ℤ) ≤ ofs) (fact3 : ofs ≤ length r) (fact4 : ofs + len ≤ length r) : (match r with | rope.Emp => True | rope.Str s ofs' _ => True | rope.App r1 r2 _ => (let left1 : ℤ := length r1 - ofs; let right1 : ℤ := len - left1; if right1 ≤ (0 : ℤ) then (match r with | rope.Emp => False | rope.Str _ _ _ => False | rope.App f f1 _ => f = r1 ∨ f1 = r1) ∧ inv r1 ∧ (0 : ℤ) ≤ len ∧ ((0 : ℤ) ≤ ofs ∧ ofs ≤ length r1) ∧ ofs + len ≤ length r1 else if left1 ≤ (0 : ℤ) then let o1 : ℤ := -left1; (match r with | rope.Emp => False | rope.Str _ _ _ => False | rope.App f f1 _ => f = r2 ∨ f1 = r2) ∧ inv r2 ∧ (0 : ℤ) ≤ len ∧ ((0 : ℤ) ≤ o1 ∧ o1 ≤ length r2) ∧ o1 + len ≤ length r2 else ((match r with | rope.Emp => False | rope.Str _ _ _ => False | rope.App f f1 _ => f = r2 ∨ f1 = r2) ∧ inv r2 ∧ (0 : ℤ) ≤ right1 ∧ ((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ length r2) ∧ (0 : ℤ) + right1 ≤ length r2) ∧ (∀(o1 : rope), inv o1 ∧ MyString.infix_eqeq (string o1) (MyString.sub (string r2) (0 : ℤ) right1) → ((match r with | rope.Emp => False | rope.Str _ _ _ => False | rope.App f f1 _ => f = r1 ∨ f1 = r1) ∧ inv r1 ∧ (0 : ℤ) ≤ left1 ∧ ((0 : ℤ) ≤ ofs ∧ ofs ≤ length r1) ∧ ofs + left1 ≤ length r1) ∧ (∀(o2 : rope), inv o2 ∧ MyString.infix_eqeq (string o2) (MyString.sub (string r1) ofs left1) → inv o2 ∧ inv o1)))) ∧ (∀(result : rope), (match r with | rope.Emp => result = rope.Emp | rope.Str s ofs' _ => (if len = (0 : ℤ) then result = rope.Emp else result = rope.Str s (ofs' + ofs) len) | rope.App r1 r2 _ => (let left1 : ℤ := length r1 - ofs; let right1 : ℤ := len - left1; if right1 ≤ (0 : ℤ) then inv result ∧ MyString.infix_eqeq (string result) (MyString.sub (string r1) ofs len) else if left1 ≤ (0 : ℤ) then inv result ∧ MyString.infix_eqeq (string result) (MyString.sub (string r2) (-left1) len) else ∃(o1 : rope), (inv o1 ∧ MyString.infix_eqeq (string o1) (MyString.sub (string r2) (0 : ℤ) right1)) ∧ (∃(o2 : rope), (inv o2 ∧ MyString.infix_eqeq (string o2) (MyString.sub (string r1) ofs left1)) ∧ inv result ∧ MyString.infix_eqeq (string result) (MyString.app (string o2) (string o1))))) → inv result ∧ MyString.infix_eqeq (string result) (MyString.sub (string r) ofs len))
  := sorry
end ropes_Rope_subqtvc
