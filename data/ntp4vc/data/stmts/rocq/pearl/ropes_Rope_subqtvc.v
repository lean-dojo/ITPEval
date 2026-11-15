From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import ropes_vcg.ropes.MyString.
Open Scope Z_scope.
Inductive rope :=
  | Emp : rope
  | Str : char_string -> Z -> Z -> rope
  | App : rope -> rope -> Z -> rope.
Axiom rope_inhabited : Inhabited rope.
Global Existing Instance rope_inhabited.
Axiom rope_countable : Countable rope.
Global Existing Instance rope_countable.
Definition length (r : rope) : Z := match r with | Emp => 0%Z | Str _ _ len => len | App _ _ len => len end.
Program Fixpoint inv (r : rope) : Prop :=
match r with | Emp => True | Str s ofs len => 0%Z < len ∧ (0%Z ≤ ofs ∧ ofs < MyString.length s) ∧ ofs + len ≤ MyString.length s | App l r1 len => 0%Z < length l ∧ inv l ∧ 0%Z < length r1 ∧ inv r1 ∧ len = length l + length r1 end.
Admit Obligations.
Program Fixpoint string (r : rope) : char_string :=
match r with | Emp => empty | Str s ofs len => sub s ofs len | App l r1 _ => MyString.app (string l) (string r1) end.
Admit Obligations.
Axiom empty : rope.
Axiom empty'def : length empty = 0%Z ∧ inv empty ∧ infix_eqeq (string empty) MyString.empty.
Theorem sub'vc (r : rope) (len : Z) (ofs : Z) (fact0 : inv r) (fact1 : 0%Z ≤ len) (fact2 : 0%Z ≤ ofs) (fact3 : ofs ≤ length r) (fact4 : ofs + len ≤ length r) : (match r with | Emp => True | Str s ofs' _ => True | App r1 r2 _ => (let left1 : Z := length r1 - ofs in let right1 : Z := len - left1 in if decide (right1 ≤ 0%Z) then (match r with | Emp => False | Str _ _ _ => False | App f f1 _ => f = r1 ∨ f1 = r1 end) ∧ inv r1 ∧ 0%Z ≤ len ∧ (0%Z ≤ ofs ∧ ofs ≤ length r1) ∧ ofs + len ≤ length r1 else if decide (left1 ≤ 0%Z) then let o1 : Z := - left1 in (match r with | Emp => False | Str _ _ _ => False | App f f1 _ => f = r2 ∨ f1 = r2 end) ∧ inv r2 ∧ 0%Z ≤ len ∧ (0%Z ≤ o1 ∧ o1 ≤ length r2) ∧ o1 + len ≤ length r2 else ((match r with | Emp => False | Str _ _ _ => False | App f f1 _ => f = r2 ∨ f1 = r2 end) ∧ inv r2 ∧ 0%Z ≤ right1 ∧ (0%Z ≤ 0%Z ∧ 0%Z ≤ length r2) ∧ 0%Z + right1 ≤ length r2) ∧ (∀(o1 : rope), inv o1 ∧ infix_eqeq (string o1) (sub (string r2) 0%Z right1) -> ((match r with | Emp => False | Str _ _ _ => False | App f f1 _ => f = r1 ∨ f1 = r1 end) ∧ inv r1 ∧ 0%Z ≤ left1 ∧ (0%Z ≤ ofs ∧ ofs ≤ length r1) ∧ ofs + left1 ≤ length r1) ∧ (∀(o2 : rope), inv o2 ∧ infix_eqeq (string o2) (sub (string r1) ofs left1) -> inv o2 ∧ inv o1))) end) ∧ (∀(result : rope), (match r with | Emp => result = Emp | Str s ofs' _ => (if decide (len = 0%Z) then result = Emp else result = Str s (ofs' + ofs) len) | App r1 r2 _ => (let left1 : Z := length r1 - ofs in let right1 : Z := len - left1 in if decide (right1 ≤ 0%Z) then inv result ∧ infix_eqeq (string result) (sub (string r1) ofs len) else if decide (left1 ≤ 0%Z) then inv result ∧ infix_eqeq (string result) (sub (string r2) (- left1) len) else ∃(o1 : rope), (inv o1 ∧ infix_eqeq (string o1) (sub (string r2) 0%Z right1)) ∧ (∃(o2 : rope), (inv o2 ∧ infix_eqeq (string o2) (sub (string r1) ofs left1)) ∧ inv result ∧ infix_eqeq (string result) (MyString.app (string o2) (string o1)))) end) -> inv result ∧ infix_eqeq (string result) (sub (string r) ofs len)).
Admitted.
