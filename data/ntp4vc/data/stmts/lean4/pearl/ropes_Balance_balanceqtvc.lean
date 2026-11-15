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
namespace Fibonacci
axiom fib : ℤ -> ℤ
axiom fib'def (n : ℤ) (fact0 : (0 : ℤ) ≤ n) : if n = (0 : ℤ) then fib n = (0 : ℤ) else if n = (1 : ℤ) then fib n = (1 : ℤ) else fib n = fib (n - (1 : ℤ)) + fib (n - (2 : ℤ))
end Fibonacci
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
namespace Rope
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
end Rope
namespace ropes_Balance_balanceqtvc
axiom max : ℤ
axiom max'def : (2 : ℤ) ≤ max
axiom string_of_array : List Rope.rope -> ℤ -> ℤ -> MyString.char_string
axiom string_of_array_empty (l : ℤ) (q : List Rope.rope) (fact0 : (0 : ℤ) ≤ l) (fact1 : l ≤ Int.ofNat (List.length q)) : MyString.infix_eqeq (string_of_array q l l) MyString.empty
axiom string_of_array_concat_left (l : ℤ) (u : ℤ) (q : List Rope.rope) (fact0 : (0 : ℤ) ≤ l) (fact1 : l < u) (fact2 : u ≤ Int.ofNat (List.length q)) : MyString.infix_eqeq (string_of_array q l u) (MyString.app (string_of_array q (l + (1 : ℤ)) u) (Rope.string (q[Int.toNat l]!)))
noncomputable def string_of_queue (q : List Rope.rope) := string_of_array q (2 : ℤ) (Int.ofNat (List.length q))
theorem balance'vc (r : Rope.rope) (fact0 : Rope.inv r) (fact1 : Rope.length r < Fibonacci.fib (max + (1 : ℤ))) : let o1 : ℤ := max + (1 : ℤ); (0 : ℤ) ≤ o1 ∧ (∀(q : List Rope.rope), (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < o1 → q[Int.toNat i]! = Rope.rope.Emp) ∧ Int.ofNat (List.length q) = o1 → (((2 : ℤ) < Int.ofNat (List.length q) ∧ Int.ofNat (List.length q) = max + (1 : ℤ)) ∧ Rope.inv r ∧ (∀(j : ℤ), (2 : ℤ) ≤ j ∧ j ≤ max → Rope.inv (q[Int.toNat j]!)) ∧ MyString.length (string_of_queue q) + Rope.length r < Fibonacci.fib (max + (1 : ℤ))) ∧ (∀(q1 : List Rope.rope), List.length q1 = List.length q → (∀(j : ℤ), (2 : ℤ) ≤ j ∧ j ≤ max → Rope.inv (q1[Int.toNat j]!)) ∧ MyString.infix_eqeq (string_of_queue q1) (MyString.app (string_of_queue q) (Rope.string r)) → (let o2 : ℤ := max; ((2 : ℤ) ≤ o2 + (1 : ℤ) → (Rope.inv Rope.rope.Emp ∧ MyString.infix_eqeq (Rope.string Rope.rope.Emp) (string_of_array q1 (2 : ℤ) (2 : ℤ))) ∧ (∀(res : Rope.rope), (∀(i : ℤ), ((2 : ℤ) ≤ i ∧ i ≤ o2) ∧ Rope.inv res ∧ MyString.infix_eqeq (Rope.string res) (string_of_array q1 (2 : ℤ) i) → ((0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length q1)) ∧ (let o3 : Rope.rope := q1[Int.toNat i]!; (Rope.inv o3 ∧ Rope.inv res) ∧ (∀(o4 : Rope.rope), Rope.inv o4 ∧ MyString.infix_eqeq (Rope.string o4) (MyString.app (Rope.string o3) (Rope.string res)) → Rope.inv o4 ∧ MyString.infix_eqeq (Rope.string o4) (string_of_array q1 (2 : ℤ) (i + (1 : ℤ)))))) ∧ (Rope.inv res ∧ MyString.infix_eqeq (Rope.string res) (string_of_array q1 (2 : ℤ) (o2 + (1 : ℤ))) → Rope.inv res ∧ MyString.infix_eqeq (Rope.string res) (Rope.string r)))) ∧ (o2 + (1 : ℤ) < (2 : ℤ) → (let result : Rope.rope := Rope.rope.Emp; Rope.inv result ∧ MyString.infix_eqeq (Rope.string result) (Rope.string r))))))
  := sorry
end ropes_Balance_balanceqtvc
