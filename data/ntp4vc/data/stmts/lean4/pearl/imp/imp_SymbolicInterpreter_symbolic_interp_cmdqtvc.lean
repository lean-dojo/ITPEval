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

namespace Syntax
axiom program_var : Type
axiom inhabited_axiom_program_var : Inhabited program_var
attribute [instance] inhabited_axiom_program_var
inductive expr where
  | Elit : ℤ -> expr
  | Evar : program_var -> expr
  | Esub : expr -> expr -> expr
axiom inhabited_axiom_expr : Inhabited expr
attribute [instance] inhabited_axiom_expr
inductive cmd where
  | Cskip : cmd
  | Cassign : program_var -> expr -> cmd
  | Cseq : cmd -> cmd -> cmd
  | Cif : expr -> cmd -> cmd -> cmd
  | Cwhile : expr -> cmd -> cmd
axiom inhabited_axiom_cmd : Inhabited cmd
attribute [instance] inhabited_axiom_cmd
end Syntax
namespace ConcreteSemantics
axiom environment : Type
axiom inhabited_axiom_environment : Inhabited environment
attribute [instance] inhabited_axiom_environment
inductive expr_behaviour where
  | Enormal : ℤ -> expr_behaviour
  | Eunbound_var : expr_behaviour
axiom inhabited_axiom_expr_behaviour : Inhabited expr_behaviour
attribute [instance] inhabited_axiom_expr_behaviour
inductive eval_expr : (Syntax.program_var -> Option ℤ) -> Syntax.expr -> expr_behaviour -> Prop where
 | eval_lit (env : Syntax.program_var -> Option ℤ) (n : ℤ) : eval_expr env (Syntax.expr.Elit n) (expr_behaviour.Enormal n)
 | eval_var (env : Syntax.program_var -> Option ℤ) (x : Syntax.program_var) (n : ℤ) : env x = Option.some n → eval_expr env (Syntax.expr.Evar x) (expr_behaviour.Enormal n)
 | eval_var_undefined (env : Syntax.program_var -> Option ℤ) (x : Syntax.program_var) : env x = Option.none → eval_expr env (Syntax.expr.Evar x) expr_behaviour.Eunbound_var
 | eval_sub (env : Syntax.program_var -> Option ℤ) (e1 : Syntax.expr) (n1 : ℤ) (e2 : Syntax.expr) (n2 : ℤ) : eval_expr env e1 (expr_behaviour.Enormal n1) → eval_expr env e2 (expr_behaviour.Enormal n2) → eval_expr env (Syntax.expr.Esub e1 e2) (expr_behaviour.Enormal (n1 - n2))
 | eval_sub_error1 (env : Syntax.program_var -> Option ℤ) (e1 : Syntax.expr) (e2 : Syntax.expr) : eval_expr env e1 expr_behaviour.Eunbound_var → eval_expr env (Syntax.expr.Esub e1 e2) expr_behaviour.Eunbound_var
 | eval_sub_error2 (env : Syntax.program_var -> Option ℤ) (e1 : Syntax.expr) (n1 : ℤ) (e2 : Syntax.expr) : eval_expr env e1 (expr_behaviour.Enormal n1) → eval_expr env e2 expr_behaviour.Eunbound_var → eval_expr env (Syntax.expr.Esub e1 e2) expr_behaviour.Eunbound_var
noncomputable def identifiers_in_expr : Syntax.expr -> Finset Syntax.program_var
  | (Syntax.expr.Elit x) => (∅ : Finset Syntax.program_var)
  | (Syntax.expr.Evar v) => insert v (∅ : Finset Syntax.program_var)
  | (Syntax.expr.Esub e1 e2) => identifiers_in_expr e1 ∪ identifiers_in_expr e2
inductive behavior where
  | Cnormal : behavior
  | Cunbound_var : behavior
  | Cloop_limit : behavior
axiom inhabited_axiom_behavior : Inhabited behavior
attribute [instance] inhabited_axiom_behavior
axiom config : Type
axiom inhabited_axiom_config : Inhabited config
attribute [instance] inhabited_axiom_config
axiom loop_limit : config -> Option ℤ
axiom config'invariant (self : config) : match loop_limit self with | Option.none => True | Option.some n => (0 : ℤ) ≤ n
noncomputable def config'eq (a : config) (b : config) := loop_limit a = loop_limit b
axiom config'inj (a : config) (b : config) (fact0 : config'eq a b) : a = b
axiom no_limit_cnf : config
axiom no_limit_cnf'def : loop_limit no_limit_cnf = Option.none
axiom mk_loop_cnf : ℤ -> config
axiom mk_loop_cnf'def (n : ℤ) (fact0 : (0 : ℤ) ≤ n) : loop_limit (mk_loop_cnf n) = Option.some n
mutual
inductive exec_cmd : config -> (Syntax.program_var -> Option ℤ) -> Syntax.cmd -> (Syntax.program_var -> Option ℤ) -> behavior -> Prop where
 | exec_skip (cnf : config) (env : Syntax.program_var -> Option ℤ) : exec_cmd cnf env Syntax.cmd.Cskip env behavior.Cnormal
 | exec_assign (env : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (n : ℤ) (cnf : config) (v : Syntax.program_var) : eval_expr env e (expr_behaviour.Enormal n) → exec_cmd cnf env (Syntax.cmd.Cassign v e) (Function.update env v (Option.some n)) behavior.Cnormal
 | exec_assign_error (env : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (cnf : config) (v : Syntax.program_var) : eval_expr env e expr_behaviour.Eunbound_var → exec_cmd cnf env (Syntax.cmd.Cassign v e) env behavior.Cunbound_var
 | exec_seq (cnf : config) (env1 : Syntax.program_var -> Option ℤ) (c1 : Syntax.cmd) (env2 : Syntax.program_var -> Option ℤ) (c2 : Syntax.cmd) (env3 : Syntax.program_var -> Option ℤ) (bhv : behavior) : exec_cmd cnf env1 c1 env2 behavior.Cnormal → exec_cmd cnf env2 c2 env3 bhv → exec_cmd cnf env1 (Syntax.cmd.Cseq c1 c2) env3 bhv
 | exec_seq_error (cnf : config) (env1 : Syntax.program_var -> Option ℤ) (c1 : Syntax.cmd) (env2 : Syntax.program_var -> Option ℤ) (bhv : behavior) (c2 : Syntax.cmd) : exec_cmd cnf env1 c1 env2 bhv → ¬bhv = behavior.Cnormal → exec_cmd cnf env1 (Syntax.cmd.Cseq c1 c2) env2 bhv
 | exec_if_false (env : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (cnf : config) (c2 : Syntax.cmd) (env' : Syntax.program_var -> Option ℤ) (bhv : behavior) (c1 : Syntax.cmd) : eval_expr env e (expr_behaviour.Enormal (0 : ℤ)) → exec_cmd cnf env c2 env' bhv → exec_cmd cnf env (Syntax.cmd.Cif e c1 c2) env' bhv
 | exec_if_true (n : ℤ) (env : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (cnf : config) (c1 : Syntax.cmd) (env' : Syntax.program_var -> Option ℤ) (bhv : behavior) (c2 : Syntax.cmd) : ¬n = (0 : ℤ) → eval_expr env e (expr_behaviour.Enormal n) → exec_cmd cnf env c1 env' bhv → exec_cmd cnf env (Syntax.cmd.Cif e c1 c2) env' bhv
 | exec_if_error (env : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (cnf : config) (c1 : Syntax.cmd) (c2 : Syntax.cmd) : eval_expr env e expr_behaviour.Eunbound_var → exec_cmd cnf env (Syntax.cmd.Cif e c1 c2) env behavior.Cunbound_var
 | exec_while1 (cnf : config) (env : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (c : Syntax.cmd) (env' : Syntax.program_var -> Option ℤ) (bhv : behavior) : exec_while cnf (0 : ℤ) env e c env' bhv → exec_cmd cnf env (Syntax.cmd.Cwhile e c) env' bhv
inductive exec_while : config -> ℤ -> (Syntax.program_var -> Option ℤ) -> Syntax.expr -> Syntax.cmd -> (Syntax.program_var -> Option ℤ) -> behavior -> Prop where
 | exec_while_overflow (cnf : config) (ctr : ℤ) (env : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (c : Syntax.cmd) : (match loop_limit cnf with | Option.none => False | Option.some n => n ≤ ctr) → exec_while cnf ctr env e c env behavior.Cloop_limit
 | exec_while_false (cnf : config) (ctr : ℤ) (env : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (c : Syntax.cmd) : (match loop_limit cnf with | Option.none => True | Option.some n => ctr < n) → eval_expr env e (expr_behaviour.Enormal (0 : ℤ)) → exec_while cnf ctr env e c env behavior.Cnormal
 | exec_while_test_error (cnf : config) (ctr : ℤ) (env : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (c : Syntax.cmd) : (match loop_limit cnf with | Option.none => True | Option.some n => ctr < n) → eval_expr env e expr_behaviour.Eunbound_var → exec_while cnf ctr env e c env behavior.Cunbound_var
 | exec_while_body_error (cnf : config) (ctr : ℤ) (env1 : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (v : ℤ) (c : Syntax.cmd) (env2 : Syntax.program_var -> Option ℤ) (bhv : behavior) : (match loop_limit cnf with | Option.none => True | Option.some n => ctr < n) → eval_expr env1 e (expr_behaviour.Enormal v) → ¬v = (0 : ℤ) → exec_cmd cnf env1 c env2 bhv → ¬bhv = behavior.Cnormal → exec_while cnf ctr env1 e c env2 bhv
 | exec_while_loop (cnf : config) (ctr : ℤ) (env1 : Syntax.program_var -> Option ℤ) (e : Syntax.expr) (v : ℤ) (c : Syntax.cmd) (env2 : Syntax.program_var -> Option ℤ) (env3 : Syntax.program_var -> Option ℤ) (bhv : behavior) : (match loop_limit cnf with | Option.none => True | Option.some n => ctr < n) → eval_expr env1 e (expr_behaviour.Enormal v) → ¬v = (0 : ℤ) → exec_cmd cnf env1 c env2 behavior.Cnormal → exec_while cnf (ctr + (1 : ℤ)) env2 e c env3 bhv → exec_while cnf ctr env1 e c env3 bhv
end
end ConcreteSemantics
namespace Svar
axiom svar : Type
axiom inhabited_axiom_svar : Inhabited svar
attribute [instance] inhabited_axiom_svar
axiom eq : svar -> svar -> Prop
axiom eq'spec (v1 : svar) (v2 : svar) : eq v1 v2 = (v1 = v2)
axiom set : Type
axiom inhabited_axiom_set : Inhabited set
attribute [instance] inhabited_axiom_set
axiom to_fset : set -> Finset svar
axiom mk : Finset svar -> set
axiom mk'spec (s : Finset svar) : to_fset (mk s) = s
axiom choose1 : set -> svar
axiom choose'spec (s : set) (fact0 : ¬to_fset s = ∅) : choose1 s ∈ to_fset s
end Svar
namespace Constraint
axiom model : Type
axiom inhabited_axiom_model : Inhabited model
attribute [instance] inhabited_axiom_model
axiom t : Type
axiom inhabited_axiom_t : Inhabited t
attribute [instance] inhabited_axiom_t
axiom model1 : t -> Syntax.program_var -> Option Svar.svar
axiom empty : t
axiom empty1 (k : Syntax.program_var) : model1 empty k = Option.none
noncomputable def get (d : t) (k : Syntax.program_var) := model1 d k
axiom set : t -> Syntax.program_var -> Svar.svar -> t
axiom set'spec'0 (d : t) (k : Syntax.program_var) (v : Svar.svar) : get (set d k v) k = Option.some v
axiom set'spec (k' : Syntax.program_var) (k : Syntax.program_var) (d : t) (v : Svar.svar) (fact0 : ¬k' = k) : get (set d k v) k' = get d k'
axiom rho : Type
axiom inhabited_axiom_rho : Inhabited rho
attribute [instance] inhabited_axiom_rho
inductive symbolic_expr where
  | Slit : ℤ -> symbolic_expr
  | Svar : Svar.svar -> symbolic_expr
  | Ssub : symbolic_expr -> symbolic_expr -> symbolic_expr
axiom inhabited_axiom_symbolic_expr : Inhabited symbolic_expr
attribute [instance] inhabited_axiom_symbolic_expr
noncomputable def interp_symbolic_expr : (Svar.svar -> ℤ) -> symbolic_expr -> ℤ
  | rho1, (symbolic_expr.Slit n) => n
  | rho1, (symbolic_expr.Svar v) => rho1 v
  | rho1, (symbolic_expr.Ssub e1 e2) => interp_symbolic_expr rho1 e1 - interp_symbolic_expr rho1 e2
inductive constr where
  | Ctrue : constr
  | Cfalse : constr
  | Ceq : symbolic_expr -> symbolic_expr -> constr
  | Cneq : symbolic_expr -> symbolic_expr -> constr
  | Cconj : constr -> constr -> constr
  | Cexists : Svar.svar -> constr -> constr
axiom inhabited_axiom_constr : Inhabited constr
attribute [instance] inhabited_axiom_constr
noncomputable def is_solution : (Svar.svar -> ℤ) -> constr -> Prop
  | rho1, constr.Ctrue => True
  | rho1, constr.Cfalse => False
  | rho1, (constr.Ceq e1 e2) => interp_symbolic_expr rho1 e1 = interp_symbolic_expr rho1 e2
  | rho1, (constr.Cneq e1 e2) => ¬interp_symbolic_expr rho1 e1 = interp_symbolic_expr rho1 e2
  | rho1, (constr.Cconj c1 c2) => is_solution rho1 c1 ∧ is_solution rho1 c2
  | rho1, (constr.Cexists x c1) => is_solution rho1 c1
noncomputable def vars_in_symbolic_expr : symbolic_expr -> Finset Svar.svar
  | (symbolic_expr.Slit x) => (∅ : Finset Svar.svar)
  | (symbolic_expr.Svar v) => insert v (∅ : Finset Svar.svar)
  | (symbolic_expr.Ssub e1 e2) => vars_in_symbolic_expr e1 ∪ vars_in_symbolic_expr e2
noncomputable def vars_in_constraint : constr -> Finset Svar.svar
  | constr.Ctrue => (∅ : Finset Svar.svar)
  | constr.Cfalse => (∅ : Finset Svar.svar)
  | (constr.Ceq e1 e2) => vars_in_symbolic_expr e1 ∪ vars_in_symbolic_expr e2
  | (constr.Cneq e1 e2) => vars_in_symbolic_expr e1 ∪ vars_in_symbolic_expr e2
  | (constr.Cconj c1 c2) => vars_in_constraint c1 ∪ vars_in_constraint c2
  | (constr.Cexists v c1) => insert v (vars_in_constraint c1)
noncomputable def existential_vars_in_constraint : constr -> Finset Svar.svar
  | constr.Ctrue => (∅ : Finset Svar.svar)
  | constr.Cfalse => (∅ : Finset Svar.svar)
  | (constr.Ceq e1 e2) => vars_in_symbolic_expr e1 ∪ vars_in_symbolic_expr e2
  | (constr.Cneq e1 e2) => vars_in_symbolic_expr e1 ∪ vars_in_symbolic_expr e2
  | (constr.Cconj c1 c2) => existential_vars_in_constraint c1 ∪ existential_vars_in_constraint c2
  | (constr.Cexists v c1) => Finset.erase (existential_vars_in_constraint c1) v
noncomputable def free_vars_in_constraint (c : constr) := vars_in_constraint c \ existential_vars_in_constraint c
noncomputable def entails (c1 : constr) (c2 : constr) := ∀(rho1 : Svar.svar -> ℤ), is_solution rho1 c1 → is_solution rho1 c2
end Constraint
namespace SymState
axiom sym_state : Type
axiom inhabited_axiom_sym_state : Inhabited sym_state
attribute [instance] inhabited_axiom_sym_state
axiom sigma : sym_state -> Constraint.t
axiom constr : sym_state -> Constraint.constr
axiom rho : sym_state -> Svar.svar -> ℤ
axiom vars : sym_state -> Svar.set
axiom sym_state'invariant (self : sym_state) : Constraint.vars_in_constraint (constr self) ⊆ Svar.to_fset (vars self) ∧ (∀(x : Syntax.program_var) (v : Svar.svar), Constraint.get (sigma self) x = Option.some v → v ∈ Svar.to_fset (vars self))
noncomputable def sym_state'eq (a : sym_state) (b : sym_state) := sigma a = sigma b ∧ constr a = constr b ∧ rho a = rho b ∧ vars a = vars b
axiom sym_state'inj (a : sym_state) (b : sym_state) (fact0 : sym_state'eq a b) : a = b
axiom eq : sym_state -> sym_state -> Prop
axiom eq'spec (s1 : sym_state) (s2 : sym_state) : eq s1 s2 = (s1 = s2)
axiom mk_sym_state : Constraint.t -> Constraint.constr -> Svar.set -> (Svar.svar -> ℤ) -> sym_state
axiom mk_sym_state'spec'2 (constr1 : Constraint.constr) (vars1 : Svar.set) (sigma1 : Constraint.t) (rho1 : Svar.svar -> ℤ) (fact0 : Constraint.vars_in_constraint constr1 ⊆ Svar.to_fset vars1) (fact1 : ∀(x : Syntax.program_var) (v : Svar.svar), Constraint.get sigma1 x = Option.some v → v ∈ Svar.to_fset vars1) : sigma (mk_sym_state sigma1 constr1 vars1 rho1) = sigma1
axiom mk_sym_state'spec'1 (constr1 : Constraint.constr) (vars1 : Svar.set) (sigma1 : Constraint.t) (rho1 : Svar.svar -> ℤ) (fact0 : Constraint.vars_in_constraint constr1 ⊆ Svar.to_fset vars1) (fact1 : ∀(x : Syntax.program_var) (v : Svar.svar), Constraint.get sigma1 x = Option.some v → v ∈ Svar.to_fset vars1) : constr (mk_sym_state sigma1 constr1 vars1 rho1) = constr1
axiom mk_sym_state'spec'0 (constr1 : Constraint.constr) (vars1 : Svar.set) (sigma1 : Constraint.t) (rho1 : Svar.svar -> ℤ) (fact0 : Constraint.vars_in_constraint constr1 ⊆ Svar.to_fset vars1) (fact1 : ∀(x : Syntax.program_var) (v : Svar.svar), Constraint.get sigma1 x = Option.some v → v ∈ Svar.to_fset vars1) : vars (mk_sym_state sigma1 constr1 vars1 rho1) = vars1
axiom mk_sym_state'spec (constr1 : Constraint.constr) (vars1 : Svar.set) (sigma1 : Constraint.t) (rho1 : Svar.svar -> ℤ) (fact0 : Constraint.vars_in_constraint constr1 ⊆ Svar.to_fset vars1) (fact1 : ∀(x : Syntax.program_var) (v : Svar.svar), Constraint.get sigma1 x = Option.some v → v ∈ Svar.to_fset vars1) : rho (mk_sym_state sigma1 constr1 vars1 rho1) = rho1
end SymState
namespace FreshSvar
noncomputable def is_fresh (v : Svar.svar) (vars : Finset Svar.svar) := ¬v ∈ vars
end FreshSvar
namespace SymStateSet
axiom set : Type
axiom inhabited_axiom_set : Inhabited set
attribute [instance] inhabited_axiom_set
axiom to_fset : set -> Finset SymState.sym_state
axiom mk : Finset SymState.sym_state -> set
axiom mk'spec (s : Finset SymState.sym_state) : to_fset (mk s) = s
axiom choose1 : set -> SymState.sym_state
axiom choose'spec (s : set) (fact0 : ¬to_fset s = ∅) : choose1 s ∈ to_fset s
axiom to_list : set -> List SymState.sym_state
axiom to_list'spec (e : SymState.sym_state) (s : set) : (e ∈ to_fset s) = (e ∈ to_list s)
axiom of_list : List SymState.sym_state -> set
axiom of_list'spec (e : SymState.sym_state) (l : List SymState.sym_state) : (e ∈ to_fset (of_list l)) = (e ∈ l)
end SymStateSet
namespace imp_SymbolicInterpreter_symbolic_interp_cmdqtvc
axiom compose : (Svar.svar -> ℤ) -> Constraint.t -> Syntax.program_var -> Option ℤ
axiom compose'def (rho : Svar.svar -> ℤ) (sigma : Constraint.t) (x : Syntax.program_var) : compose rho sigma x = (match Constraint.get sigma x with | Option.some v => Option.some (rho v) | Option.none => Option.none)
noncomputable def state_extends (s : SymState.sym_state) (s' : SymState.sym_state) := Svar.to_fset (SymState.vars s) ⊆ Svar.to_fset (SymState.vars s') ∧ (∀(v : Svar.svar), v ∈ Svar.to_fset (SymState.vars s) → SymState.rho s v = SymState.rho s' v)
axiom svar_set_add : Svar.svar -> Svar.set -> Svar.set
axiom svar_set_add'def (v : Svar.svar) (vs : Svar.set) : Svar.to_fset (svar_set_add v vs) = insert v (Svar.to_fset vs) ∧ (if v ∈ Svar.to_fset vs then Finset.card (Svar.to_fset (svar_set_add v vs)) = Finset.card (Svar.to_fset vs) else Int.ofNat (Finset.card (Svar.to_fset (svar_set_add v vs))) = Int.ofNat (Finset.card (Svar.to_fset vs)) + (1 : ℤ))
noncomputable def results_extend (s : SymState.sym_state) (normals : Finset SymState.sym_state) (unbounds : Finset SymState.sym_state) (limits : Finset SymState.sym_state) := ∀(s' : SymState.sym_state), s' ∈ normals ∨ s' ∈ unbounds ∨ s' ∈ limits → state_extends s s'
theorem symbolic_interp_cmd'vc (n : ℤ) (c : Syntax.cmd) (s : SymState.sym_state) (fact0 : (0 : ℤ) ≤ n) : (match c with | Syntax.cmd.Cskip => True | Syntax.cmd.Cassign x e => (∀(se : Constraint.symbolic_expr), ConcreteSemantics.eval_expr (compose (SymState.rho s) (SymState.sigma s)) e (ConcreteSemantics.expr_behaviour.Enormal (Constraint.interp_symbolic_expr (SymState.rho s) se)) ∧ (∀(v : Svar.svar), v ∈ Constraint.vars_in_symbolic_expr se → (∃(x1 : Syntax.program_var), Constraint.get (SymState.sigma s) x1 = Option.some v)) → (∀(v' : Svar.svar), FreshSvar.is_fresh v' (Svar.to_fset (SymState.vars s)) → (let o1 : Constraint.t := SymState.sigma s; let sigma' : Constraint.t := Constraint.set o1 x v'; Constraint.get sigma' x = Option.some v' ∧ (∀(k' : Syntax.program_var), ¬k' = x → Constraint.get sigma' k' = Constraint.get o1 k') → (∀(constr' : Constraint.constr), (let constr : Constraint.constr := Constraint.constr.Cconj (SymState.constr s) (Constraint.constr.Ceq (Constraint.symbolic_expr.Svar v') se); (∃(v : Svar.svar), (match Constraint.get (SymState.sigma s) x with | Option.none => False | Option.some v1 => v = v1) ∧ (∀(rho : Svar.svar -> ℤ), Constraint.is_solution rho constr' = Constraint.is_solution rho (Constraint.constr.Cexists v constr)) ∧ Constraint.vars_in_constraint constr' ⊆ Constraint.vars_in_constraint (Constraint.constr.Cexists v constr)) ∨ Constraint.get (SymState.sigma s) x = Option.none ∧ constr' = constr) → (let o2 : Svar.set := SymState.vars s; ∀(vars' : Svar.set), Svar.to_fset vars' = insert v' (Svar.to_fset o2) ∧ (if v' ∈ Svar.to_fset o2 then Finset.card (Svar.to_fset vars') = Finset.card (Svar.to_fset o2) else Int.ofNat (Finset.card (Svar.to_fset vars')) = Int.ofNat (Finset.card (Svar.to_fset o2)) + (1 : ℤ)) → Constraint.vars_in_constraint constr' ⊆ Svar.to_fset vars' ∧ (∀(x1 : Syntax.program_var) (v : Svar.svar), Constraint.get sigma' x1 = Option.some v → v ∈ Svar.to_fset vars')))))) | Syntax.cmd.Cseq c1 c2 => ((match c with | Syntax.cmd.Cskip => False | Syntax.cmd.Cassign _ _ => False | Syntax.cmd.Cseq f f1 => f = c1 ∨ f1 = c1 | Syntax.cmd.Cif _ f f1 => f = c1 ∨ f1 = c1 | Syntax.cmd.Cwhile _ f => f = c1) ∧ (0 : ℤ) ≤ n) ∧ (∀(normals1 : SymStateSet.set) (unbounds1 : SymStateSet.set) (limits1 : SymStateSet.set), results_extend s (SymStateSet.to_fset normals1) (SymStateSet.to_fset unbounds1) (SymStateSet.to_fset limits1) ∧ (Constraint.is_solution (SymState.rho s) (SymState.constr s) → (∀(gamma' : Syntax.program_var -> Option ℤ) (bhv : ConcreteSemantics.behavior), ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s) (SymState.sigma s)) c1 gamma' bhv → (∃(s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals1 | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds1 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits1) ∧ Constraint.is_solution (SymState.rho s') (SymState.constr s') ∧ gamma' = compose (SymState.rho s') (SymState.sigma s')))) ∧ (∀(bhv : ConcreteSemantics.behavior) (s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals1 | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds1 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits1) → Constraint.is_solution (SymState.rho s') (SymState.constr s') → Constraint.is_solution (SymState.rho s) (SymState.constr s) ∧ ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s) (SymState.sigma s)) c1 (compose (SymState.rho s') (SymState.sigma s')) bhv) → (let o1 : List SymState.sym_state := SymStateSet.to_list normals1; (∀(e : SymState.sym_state), (e ∈ SymStateSet.to_fset normals1) = (e ∈ o1)) → ((match c with | Syntax.cmd.Cskip => False | Syntax.cmd.Cassign _ _ => False | Syntax.cmd.Cseq f f1 => f = c2 ∨ f1 = c2 | Syntax.cmd.Cif _ f f1 => f = c2 ∨ f1 = c2 | Syntax.cmd.Cwhile _ f => f = c2) ∨ c = c2 ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ Int.ofNat (List.length o1) < (0 : ℤ)) ∧ (0 : ℤ) ≤ n)) | Syntax.cmd.Cif e c1 c2 => (∀(se : Constraint.symbolic_expr), ConcreteSemantics.eval_expr (compose (SymState.rho s) (SymState.sigma s)) e (ConcreteSemantics.expr_behaviour.Enormal (Constraint.interp_symbolic_expr (SymState.rho s) se)) ∧ (∀(v : Svar.svar), v ∈ Constraint.vars_in_symbolic_expr se → (∃(x : Syntax.program_var), Constraint.get (SymState.sigma s) x = Option.some v)) → (let o1 : Svar.set := SymState.vars s; let o2 : Constraint.constr := Constraint.constr.Cconj (SymState.constr s) (Constraint.constr.Cneq se (Constraint.symbolic_expr.Slit (0 : ℤ))); let o3 : Constraint.t := SymState.sigma s; (Constraint.vars_in_constraint o2 ⊆ Svar.to_fset o1 ∧ (∀(x : Syntax.program_var) (v : Svar.svar), Constraint.get o3 x = Option.some v → v ∈ Svar.to_fset o1)) ∧ (∀(s1 : SymState.sym_state), SymState.sigma s1 = o3 ∧ SymState.constr s1 = o2 ∧ SymState.rho s1 = SymState.rho s ∧ SymState.vars s1 = o1 → (let o4 : Svar.set := SymState.vars s; let o5 : Constraint.constr := Constraint.constr.Cconj (SymState.constr s) (Constraint.constr.Ceq se (Constraint.symbolic_expr.Slit (0 : ℤ))); let o6 : Constraint.t := SymState.sigma s; (Constraint.vars_in_constraint o5 ⊆ Svar.to_fset o4 ∧ (∀(x : Syntax.program_var) (v : Svar.svar), Constraint.get o6 x = Option.some v → v ∈ Svar.to_fset o4)) ∧ (∀(s2 : SymState.sym_state), SymState.sigma s2 = o6 ∧ SymState.constr s2 = o5 ∧ SymState.rho s2 = SymState.rho s ∧ SymState.vars s2 = o4 → ((true = false → (∀(rho : Svar.svar -> ℤ), ¬Constraint.is_solution rho (SymState.constr s1))) → (match c with | Syntax.cmd.Cskip => False | Syntax.cmd.Cassign _ _ => False | Syntax.cmd.Cseq f f1 => f = c1 ∨ f1 = c1 | Syntax.cmd.Cif _ f f1 => f = c1 ∨ f1 = c1 | Syntax.cmd.Cwhile _ f => f = c1) ∧ (0 : ℤ) ≤ n) ∧ (∀(normals1 : SymStateSet.set) (unbounds1 : SymStateSet.set) (limits1 : SymStateSet.set), (∃(o7 : Bool), (o7 = false → (∀(rho : Svar.svar -> ℤ), ¬Constraint.is_solution rho (SymState.constr s1))) ∧ (if o7 = true then results_extend s1 (SymStateSet.to_fset normals1) (SymStateSet.to_fset unbounds1) (SymStateSet.to_fset limits1) ∧ (Constraint.is_solution (SymState.rho s1) (SymState.constr s1) → (∀(gamma' : Syntax.program_var -> Option ℤ) (bhv : ConcreteSemantics.behavior), ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s1) (SymState.sigma s1)) c1 gamma' bhv → (∃(s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals1 | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds1 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits1) ∧ Constraint.is_solution (SymState.rho s') (SymState.constr s') ∧ gamma' = compose (SymState.rho s') (SymState.sigma s')))) ∧ (∀(bhv : ConcreteSemantics.behavior) (s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals1 | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds1 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits1) → Constraint.is_solution (SymState.rho s') (SymState.constr s') → Constraint.is_solution (SymState.rho s1) (SymState.constr s1) ∧ ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s1) (SymState.sigma s1)) c1 (compose (SymState.rho s') (SymState.sigma s')) bhv) else (SymStateSet.to_fset limits1 = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset limits1)) = (0 : ℤ)) ∧ (SymStateSet.to_fset unbounds1 = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset unbounds1)) = (0 : ℤ)) ∧ SymStateSet.to_fset normals1 = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset normals1)) = (0 : ℤ))) → (true = false → (∀(rho : Svar.svar -> ℤ), ¬Constraint.is_solution rho (SymState.constr s2))) → (match c with | Syntax.cmd.Cskip => False | Syntax.cmd.Cassign _ _ => False | Syntax.cmd.Cseq f f1 => f = c2 ∨ f1 = c2 | Syntax.cmd.Cif _ f f1 => f = c2 ∨ f1 = c2 | Syntax.cmd.Cwhile _ f => f = c2) ∧ (0 : ℤ) ≤ n)))))) | Syntax.cmd.Cwhile e c1 => ((match c with | Syntax.cmd.Cskip => False | Syntax.cmd.Cassign _ _ => False | Syntax.cmd.Cseq f f1 => f = Syntax.cmd.Cwhile e c1 ∨ f1 = Syntax.cmd.Cwhile e c1 | Syntax.cmd.Cif _ f f1 => f = Syntax.cmd.Cwhile e c1 ∨ f1 = Syntax.cmd.Cwhile e c1 | Syntax.cmd.Cwhile _ f => f = Syntax.cmd.Cwhile e c1) ∨ c = Syntax.cmd.Cwhile e c1 ∧ (0 : ℤ) ≤ n + (1 : ℤ) ∧ n - (0 : ℤ) < n + (1 : ℤ)) ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ n) ∧ (∀(normals : SymStateSet.set) (unbounds : SymStateSet.set) (limits : SymStateSet.set), (match c with | Syntax.cmd.Cskip => (SymStateSet.to_fset limits = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset limits)) = (0 : ℤ)) ∧ (SymStateSet.to_fset unbounds = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset unbounds)) = (0 : ℤ)) ∧ SymStateSet.to_fset normals = insert s (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset normals)) = (1 : ℤ) | Syntax.cmd.Cassign x e => (∃(se : Constraint.symbolic_expr), (ConcreteSemantics.eval_expr (compose (SymState.rho s) (SymState.sigma s)) e (ConcreteSemantics.expr_behaviour.Enormal (Constraint.interp_symbolic_expr (SymState.rho s) se)) ∧ (∀(v : Svar.svar), v ∈ Constraint.vars_in_symbolic_expr se → (∃(x1 : Syntax.program_var), Constraint.get (SymState.sigma s) x1 = Option.some v))) ∧ (∃(v' : Svar.svar), FreshSvar.is_fresh v' (Svar.to_fset (SymState.vars s)) ∧ (let o1 : Constraint.t := SymState.sigma s; let sigma' : Constraint.t := Constraint.set o1 x v'; (Constraint.get sigma' x = Option.some v' ∧ (∀(k' : Syntax.program_var), ¬k' = x → Constraint.get sigma' k' = Constraint.get o1 k')) ∧ (∃(constr' : Constraint.constr), (let constr : Constraint.constr := Constraint.constr.Cconj (SymState.constr s) (Constraint.constr.Ceq (Constraint.symbolic_expr.Svar v') se); (∃(v : Svar.svar), (match Constraint.get (SymState.sigma s) x with | Option.none => False | Option.some v1 => v = v1) ∧ (∀(rho : Svar.svar -> ℤ), Constraint.is_solution rho constr' = Constraint.is_solution rho (Constraint.constr.Cexists v constr)) ∧ Constraint.vars_in_constraint constr' ⊆ Constraint.vars_in_constraint (Constraint.constr.Cexists v constr)) ∨ Constraint.get (SymState.sigma s) x = Option.none ∧ constr' = constr) ∧ (let o2 : Svar.set := SymState.vars s; ∃(vars' : Svar.set), (Svar.to_fset vars' = insert v' (Svar.to_fset o2) ∧ (if v' ∈ Svar.to_fset o2 then Finset.card (Svar.to_fset vars') = Finset.card (Svar.to_fset o2) else Int.ofNat (Finset.card (Svar.to_fset vars')) = Int.ofNat (Finset.card (Svar.to_fset o2)) + (1 : ℤ))) ∧ (∃(s' : SymState.sym_state), (SymState.sigma s' = sigma' ∧ SymState.constr s' = constr' ∧ SymState.rho s' = Function.update (SymState.rho s) v' (Constraint.interp_symbolic_expr (SymState.rho s) se) ∧ SymState.vars s' = vars') ∧ (SymStateSet.to_fset limits = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset limits)) = (0 : ℤ)) ∧ (SymStateSet.to_fset unbounds = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset unbounds)) = (0 : ℤ)) ∧ SymStateSet.to_fset normals = insert s' (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset normals)) = (1 : ℤ))))))) ∨ ConcreteSemantics.eval_expr (compose (SymState.rho s) (SymState.sigma s)) e ConcreteSemantics.expr_behaviour.Eunbound_var ∧ (SymStateSet.to_fset limits = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset limits)) = (0 : ℤ)) ∧ (SymStateSet.to_fset unbounds = insert s (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset unbounds)) = (1 : ℤ)) ∧ SymStateSet.to_fset normals = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset normals)) = (0 : ℤ) | Syntax.cmd.Cseq c1 c2 => (∃(normals1 : SymStateSet.set) (unbounds1 : SymStateSet.set) (limits1 : SymStateSet.set), (results_extend s (SymStateSet.to_fset normals1) (SymStateSet.to_fset unbounds1) (SymStateSet.to_fset limits1) ∧ (Constraint.is_solution (SymState.rho s) (SymState.constr s) → (∀(gamma' : Syntax.program_var -> Option ℤ) (bhv : ConcreteSemantics.behavior), ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s) (SymState.sigma s)) c1 gamma' bhv → (∃(s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals1 | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds1 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits1) ∧ Constraint.is_solution (SymState.rho s') (SymState.constr s') ∧ gamma' = compose (SymState.rho s') (SymState.sigma s')))) ∧ (∀(bhv : ConcreteSemantics.behavior) (s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals1 | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds1 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits1) → Constraint.is_solution (SymState.rho s') (SymState.constr s') → Constraint.is_solution (SymState.rho s) (SymState.constr s) ∧ ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s) (SymState.sigma s)) c1 (compose (SymState.rho s') (SymState.sigma s')) bhv)) ∧ (let o1 : List SymState.sym_state := SymStateSet.to_list normals1; (∀(e : SymState.sym_state), (e ∈ SymStateSet.to_fset normals1) = (e ∈ o1)) ∧ (∃(unbounds2 : SymStateSet.set) (limits2 : SymStateSet.set), ((∀(s' : SymState.sym_state), s' ∈ SymStateSet.to_fset normals ∨ s' ∈ SymStateSet.to_fset unbounds2 ∨ s' ∈ SymStateSet.to_fset limits2 → (∃(s1 : SymState.sym_state), s1 ∈ SymStateSet.to_fset (SymStateSet.of_list o1) ∧ state_extends s1 s')) ∧ (∀(s1 : SymState.sym_state), s1 ∈ SymStateSet.to_fset (SymStateSet.of_list o1) → Constraint.is_solution (SymState.rho s1) (SymState.constr s1) → (∀(gamma' : Syntax.program_var -> Option ℤ) (bhv : ConcreteSemantics.behavior), ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s1) (SymState.sigma s1)) c2 gamma' bhv → (∃(s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds2 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits2) ∧ Constraint.is_solution (SymState.rho s') (SymState.constr s') ∧ gamma' = compose (SymState.rho s') (SymState.sigma s')))) ∧ (∀(bhv : ConcreteSemantics.behavior) (s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds2 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits2) → Constraint.is_solution (SymState.rho s') (SymState.constr s') → (∃(s1 : SymState.sym_state), s1 ∈ SymStateSet.to_fset (SymStateSet.of_list o1) ∧ Constraint.is_solution (SymState.rho s1) (SymState.constr s1) ∧ ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s1) (SymState.sigma s1)) c2 (compose (SymState.rho s') (SymState.sigma s')) bhv))) ∧ SymStateSet.to_fset limits = SymStateSet.to_fset limits1 ∪ SymStateSet.to_fset limits2 ∧ SymStateSet.to_fset unbounds = SymStateSet.to_fset unbounds1 ∪ SymStateSet.to_fset unbounds2))) | Syntax.cmd.Cif e c1 c2 => (∃(se : Constraint.symbolic_expr), (ConcreteSemantics.eval_expr (compose (SymState.rho s) (SymState.sigma s)) e (ConcreteSemantics.expr_behaviour.Enormal (Constraint.interp_symbolic_expr (SymState.rho s) se)) ∧ (∀(v : Svar.svar), v ∈ Constraint.vars_in_symbolic_expr se → (∃(x : Syntax.program_var), Constraint.get (SymState.sigma s) x = Option.some v))) ∧ (∃(s1 : SymState.sym_state), (SymState.sigma s1 = SymState.sigma s ∧ SymState.constr s1 = Constraint.constr.Cconj (SymState.constr s) (Constraint.constr.Cneq se (Constraint.symbolic_expr.Slit (0 : ℤ))) ∧ SymState.rho s1 = SymState.rho s ∧ SymState.vars s1 = SymState.vars s) ∧ (∃(s2 : SymState.sym_state), (SymState.sigma s2 = SymState.sigma s ∧ SymState.constr s2 = Constraint.constr.Cconj (SymState.constr s) (Constraint.constr.Ceq se (Constraint.symbolic_expr.Slit (0 : ℤ))) ∧ SymState.rho s2 = SymState.rho s ∧ SymState.vars s2 = SymState.vars s) ∧ (∃(normals1 : SymStateSet.set) (unbounds1 : SymStateSet.set) (limits1 : SymStateSet.set), (∃(o1 : Bool), (o1 = false → (∀(rho : Svar.svar -> ℤ), ¬Constraint.is_solution rho (SymState.constr s1))) ∧ (if o1 = true then results_extend s1 (SymStateSet.to_fset normals1) (SymStateSet.to_fset unbounds1) (SymStateSet.to_fset limits1) ∧ (Constraint.is_solution (SymState.rho s1) (SymState.constr s1) → (∀(gamma' : Syntax.program_var -> Option ℤ) (bhv : ConcreteSemantics.behavior), ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s1) (SymState.sigma s1)) c1 gamma' bhv → (∃(s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals1 | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds1 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits1) ∧ Constraint.is_solution (SymState.rho s') (SymState.constr s') ∧ gamma' = compose (SymState.rho s') (SymState.sigma s')))) ∧ (∀(bhv : ConcreteSemantics.behavior) (s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals1 | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds1 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits1) → Constraint.is_solution (SymState.rho s') (SymState.constr s') → Constraint.is_solution (SymState.rho s1) (SymState.constr s1) ∧ ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s1) (SymState.sigma s1)) c1 (compose (SymState.rho s') (SymState.sigma s')) bhv) else (SymStateSet.to_fset limits1 = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset limits1)) = (0 : ℤ)) ∧ (SymStateSet.to_fset unbounds1 = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset unbounds1)) = (0 : ℤ)) ∧ SymStateSet.to_fset normals1 = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset normals1)) = (0 : ℤ))) ∧ (∃(normals2 : SymStateSet.set) (unbounds2 : SymStateSet.set) (limits2 : SymStateSet.set), (∃(o1 : Bool), (o1 = false → (∀(rho : Svar.svar -> ℤ), ¬Constraint.is_solution rho (SymState.constr s2))) ∧ (if o1 = true then results_extend s2 (SymStateSet.to_fset normals2) (SymStateSet.to_fset unbounds2) (SymStateSet.to_fset limits2) ∧ (Constraint.is_solution (SymState.rho s2) (SymState.constr s2) → (∀(gamma' : Syntax.program_var -> Option ℤ) (bhv : ConcreteSemantics.behavior), ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s2) (SymState.sigma s2)) c2 gamma' bhv → (∃(s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals2 | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds2 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits2) ∧ Constraint.is_solution (SymState.rho s') (SymState.constr s') ∧ gamma' = compose (SymState.rho s') (SymState.sigma s')))) ∧ (∀(bhv : ConcreteSemantics.behavior) (s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals2 | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds2 | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits2) → Constraint.is_solution (SymState.rho s') (SymState.constr s') → Constraint.is_solution (SymState.rho s2) (SymState.constr s2) ∧ ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s2) (SymState.sigma s2)) c2 (compose (SymState.rho s') (SymState.sigma s')) bhv) else (SymStateSet.to_fset limits2 = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset limits2)) = (0 : ℤ)) ∧ (SymStateSet.to_fset unbounds2 = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset unbounds2)) = (0 : ℤ)) ∧ SymStateSet.to_fset normals2 = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset normals2)) = (0 : ℤ))) ∧ SymStateSet.to_fset limits = SymStateSet.to_fset limits1 ∪ SymStateSet.to_fset limits2 ∧ SymStateSet.to_fset unbounds = SymStateSet.to_fset unbounds1 ∪ SymStateSet.to_fset unbounds2 ∧ SymStateSet.to_fset normals = SymStateSet.to_fset normals1 ∪ SymStateSet.to_fset normals2))))) ∨ ConcreteSemantics.eval_expr (compose (SymState.rho s) (SymState.sigma s)) e ConcreteSemantics.expr_behaviour.Eunbound_var ∧ (SymStateSet.to_fset limits = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset limits)) = (0 : ℤ)) ∧ (SymStateSet.to_fset unbounds = insert s (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset unbounds)) = (1 : ℤ)) ∧ SymStateSet.to_fset normals = (∅ : Finset SymState.sym_state) ∧ Int.ofNat (Finset.card (SymStateSet.to_fset normals)) = (0 : ℤ) | Syntax.cmd.Cwhile e c1 => results_extend s (SymStateSet.to_fset normals) (SymStateSet.to_fset unbounds) (SymStateSet.to_fset limits) ∧ (Constraint.is_solution (SymState.rho s) (SymState.constr s) → (∀(gamma' : Syntax.program_var -> Option ℤ) (bhv : ConcreteSemantics.behavior), ConcreteSemantics.exec_while (ConcreteSemantics.mk_loop_cnf n) (0 : ℤ) (compose (SymState.rho s) (SymState.sigma s)) e c1 gamma' bhv → (∃(s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits) ∧ Constraint.is_solution (SymState.rho s') (SymState.constr s') ∧ gamma' = compose (SymState.rho s') (SymState.sigma s')))) ∧ (∀(bhv : ConcreteSemantics.behavior) (s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits) → Constraint.is_solution (SymState.rho s') (SymState.constr s') → Constraint.is_solution (SymState.rho s) (SymState.constr s) ∧ ConcreteSemantics.exec_while (ConcreteSemantics.mk_loop_cnf n) (0 : ℤ) (compose (SymState.rho s) (SymState.sigma s)) e c1 (compose (SymState.rho s') (SymState.sigma s')) bhv)) → results_extend s (SymStateSet.to_fset normals) (SymStateSet.to_fset unbounds) (SymStateSet.to_fset limits) ∧ (Constraint.is_solution (SymState.rho s) (SymState.constr s) → (∀(gamma' : Syntax.program_var -> Option ℤ) (bhv : ConcreteSemantics.behavior), ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s) (SymState.sigma s)) c gamma' bhv → (∃(s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits) ∧ Constraint.is_solution (SymState.rho s') (SymState.constr s') ∧ gamma' = compose (SymState.rho s') (SymState.sigma s')))) ∧ (∀(bhv : ConcreteSemantics.behavior) (s' : SymState.sym_state), (match bhv with | ConcreteSemantics.behavior.Cnormal => s' ∈ SymStateSet.to_fset normals | ConcreteSemantics.behavior.Cunbound_var => s' ∈ SymStateSet.to_fset unbounds | ConcreteSemantics.behavior.Cloop_limit => s' ∈ SymStateSet.to_fset limits) → Constraint.is_solution (SymState.rho s') (SymState.constr s') → Constraint.is_solution (SymState.rho s) (SymState.constr s) ∧ ConcreteSemantics.exec_cmd (ConcreteSemantics.mk_loop_cnf n) (compose (SymState.rho s) (SymState.sigma s)) c (compose (SymState.rho s') (SymState.sigma s')) bhv))
  := sorry
end imp_SymbolicInterpreter_symbolic_interp_cmdqtvc
