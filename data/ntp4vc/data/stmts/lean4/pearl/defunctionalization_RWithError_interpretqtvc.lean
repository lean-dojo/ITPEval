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

namespace Expr
inductive expr where
  | Cte : ℤ -> expr
  | Sub : expr -> expr -> expr
axiom inhabited_axiom_expr : Inhabited expr
attribute [instance] inhabited_axiom_expr
axiom prog : Type
axiom inhabited_axiom_prog : Inhabited prog
attribute [instance] inhabited_axiom_prog
end Expr
namespace DirectSem
noncomputable def eval_0 : Expr.expr -> ℤ
  | (Expr.expr.Cte n) => n
  | (Expr.expr.Sub e1 e2) => eval_0 e1 - eval_0 e2
end DirectSem
namespace Defunctionalization
inductive cont where
  | A1 : Expr.expr -> cont -> cont
  | A2 : ℤ -> cont -> cont
  | I : cont
axiom inhabited_axiom_cont : Inhabited cont
attribute [instance] inhabited_axiom_cont
inductive eval_cont : cont -> ℤ -> ℤ -> Prop where
 | a1 (v : ℤ) (k : cont) (e2 : Expr.expr) (r : ℤ) : eval_cont (cont.A2 v k) (DirectSem.eval_0 e2) r → eval_cont (cont.A1 e2 k) v r
 | a2 (k : cont) (v1 : ℤ) (v : ℤ) (r : ℤ) : eval_cont k (v1 - v) r → eval_cont (cont.A2 v1 k) v r
 | a3 (v : ℤ) : eval_cont cont.I v v
noncomputable def size_e : Expr.expr -> ℤ
  | (Expr.expr.Cte x) => (1 : ℤ)
  | (Expr.expr.Sub e1 e2) => (3 : ℤ) + size_e e1 + size_e e2
noncomputable def size_c : cont -> ℤ
  | cont.I => (0 : ℤ)
  | (cont.A1 e2 k) => (2 : ℤ) + size_e e2 + size_c k
  | (cont.A2 x k) => (1 : ℤ) + size_c k
end Defunctionalization
namespace SemWithError
inductive value where
  | Vnum : ℤ -> value
  | Underflow : value
axiom inhabited_axiom_value : Inhabited value
attribute [instance] inhabited_axiom_value
noncomputable def eval_0 : Expr.expr -> value
  | (Expr.expr.Cte n) => if (0 : ℤ) ≤ n then value.Vnum n else value.Underflow
  | (Expr.expr.Sub e1 e2) => match eval_0 e1 with | value.Underflow => value.Underflow | value.Vnum v1 => (match eval_0 e2 with | value.Underflow => value.Underflow | value.Vnum v2 => (if v2 ≤ v1 then value.Vnum (v1 - v2) else value.Underflow))
axiom fc :  {α : Type} -> [Inhabited α] -> (value -> α) -> ℤ -> value -> α
axiom fc1 :  {α : Type} -> [Inhabited α] -> (value -> α) -> Expr.expr -> value -> α
axiom fc'def {α : Type} [Inhabited α] (k : value -> α) (v1 : ℤ) (v2 : value) : fc k v1 v2 = (match v2 with | value.Underflow => k value.Underflow | value.Vnum v21 => k (if v21 ≤ v1 then value.Vnum (v1 - v21) else value.Underflow))
noncomputable def eval_1 {α : Type} [Inhabited α] : Expr.expr -> (value -> α) -> α
  | (Expr.expr.Cte n), k => k (if (0 : ℤ) ≤ n then value.Vnum n else value.Underflow)
  | (Expr.expr.Sub e1 e2), k => eval_1 e1 (fc1 k e2)
axiom fc'def1 {α : Type} [Inhabited α] (k : value -> α) (e2 : Expr.expr) (v1 : value) : fc1 k e2 v1 = (match v1 with | value.Underflow => k value.Underflow | value.Vnum v11 => eval_1 e2 (fc k v11))
axiom identity : value -> value
axiom identity_def (y : value) : identity y = y
noncomputable def interpret_1 (p : Expr.expr) := eval_1 p identity
axiom eval_2a :  {α : Type} -> [Inhabited α] -> Expr.expr -> (ℤ -> α) -> (Unit -> α) -> ℤ -> α
axiom eval_2b :  {α : Type} -> [Inhabited α] -> ℤ -> (ℤ -> α) -> (Unit -> α) -> ℤ -> α
axiom eval_2b'def {α : Type} [Inhabited α] (v1 : ℤ) (k : ℤ -> α) (kerr : Unit -> α) (v2 : ℤ) : eval_2b v1 k kerr v2 = (if v2 ≤ v1 then k (v1 - v2) else kerr ())
noncomputable def eval_2 {α : Type} [Inhabited α] : Expr.expr -> (ℤ -> α) -> (Unit -> α) -> α
  | (Expr.expr.Cte n), k, kerr => if (0 : ℤ) ≤ n then k n else kerr ()
  | (Expr.expr.Sub e1 e2), k, kerr => eval_2 e1 (eval_2a e2 k kerr) kerr
axiom eval_2a'def {α : Type} [Inhabited α] (e2 : Expr.expr) (k : ℤ -> α) (kerr : Unit -> α) (v1 : ℤ) : eval_2a e2 k kerr v1 = eval_2 e2 (eval_2b v1 k kerr) kerr
axiom Vnum_closure : ℤ -> value
axiom fc2 : Unit -> value
axiom Vnum_closure_def (y : ℤ) : Vnum_closure y = value.Vnum y
axiom fc'def2 (x : Unit) : fc2 x = value.Underflow
noncomputable def interpret_2 (p : Expr.expr) := eval_2 p Vnum_closure fc2
axiom eval_3a : Expr.expr -> (ℤ -> value) -> ℤ -> value
axiom eval_3b : ℤ -> (ℤ -> value) -> ℤ -> value
axiom eval_3b'def (v1 : ℤ) (k : ℤ -> value) (v2 : ℤ) : eval_3b v1 k v2 = (if v2 ≤ v1 then k (v1 - v2) else value.Underflow)
noncomputable def eval_3 : Expr.expr -> (ℤ -> value) -> value
  | (Expr.expr.Cte n), k => if (0 : ℤ) ≤ n then k n else value.Underflow
  | (Expr.expr.Sub e1 e2), k => eval_3 e1 (eval_3a e2 k)
axiom eval_3a'def (e2 : Expr.expr) (k : ℤ -> value) (v1 : ℤ) : eval_3a e2 k v1 = eval_3 e2 (eval_3b v1 k)
noncomputable def interpret_3 (p : Expr.expr) := eval_3 p Vnum_closure
inductive cont where
  | I : cont
  | A : Expr.expr -> cont -> cont
  | B : ℤ -> cont -> cont
axiom inhabited_axiom_cont : Inhabited cont
attribute [instance] inhabited_axiom_cont
inductive eval_cont : cont -> value -> value -> Prop where
 | underflow (k : cont) : eval_cont k value.Underflow value.Underflow
 | a1 (v : ℤ) (k : cont) (e2 : Expr.expr) (r : value) : eval_cont (cont.B v k) (eval_0 e2) r → eval_cont (cont.A e2 k) (value.Vnum v) r
 | a2 (k : cont) (v : ℤ) (v1 : ℤ) (r : value) : eval_cont k (if v ≤ v1 then value.Vnum (v1 - v) else value.Underflow) r → eval_cont (cont.B v1 k) (value.Vnum v) r
 | a3 (v : ℤ) : eval_cont cont.I (value.Vnum v) (value.Vnum v)
noncomputable def size_e : Expr.expr -> ℤ
  | (Expr.expr.Cte x) => (1 : ℤ)
  | (Expr.expr.Sub e1 e2) => (3 : ℤ) + size_e e1 + size_e e2
noncomputable def size_c : cont -> ℤ
  | cont.I => (0 : ℤ)
  | (cont.A e2 k) => (2 : ℤ) + Defunctionalization.size_e e2 + size_c k
  | (cont.B x k) => (1 : ℤ) + size_c k
end SemWithError
namespace defunctionalization_RWithError_interpretqtvc
inductive context where
  | Empty : context
  | Left : context -> Expr.expr -> context
  | Right : ℤ -> context -> context
axiom inhabited_axiom_context : Inhabited context
attribute [instance] inhabited_axiom_context
noncomputable def size_c : context -> ℤ
  | context.Empty => (0 : ℤ)
  | (context.Left c1 e) => (2 : ℤ) + size_c c1 + Defunctionalization.size_e e
  | (context.Right x c1) => (1 : ℤ) + size_c c1
noncomputable def recompose : context -> Expr.expr -> Expr.expr
  | context.Empty, e => e
  | (context.Left c1 e2), e => recompose c1 (Expr.expr.Sub e e2)
  | (context.Right n1 c1), e => recompose c1 (Expr.expr.Sub (Expr.expr.Cte n1) e)
theorem interpret'vc (p : Expr.expr) : SemWithError.eval_0 (recompose context.Empty p) = SemWithError.eval_0 p
  := sorry
end defunctionalization_RWithError_interpretqtvc
