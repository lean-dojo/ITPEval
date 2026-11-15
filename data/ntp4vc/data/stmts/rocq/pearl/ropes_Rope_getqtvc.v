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
Theorem get'vc (r : rope) (i : Z) (fact0 : inv r) (fact1 : 0%Z ≤ i) (fact2 : i < length r) : (match r with | Emp => False | Str s ofs _ => (let o1 : Z := ofs + i in 0%Z ≤ o1 ∧ o1 < MyString.length s) | App left1 right1 _ => (let n : Z := length left1 in if decide (i < n) then (match r with | Emp => False | Str _ _ _ => False | App f f1 _ => f = left1 ∨ f1 = left1 end) ∧ inv left1 ∧ 0%Z ≤ i ∧ i < length left1 else let o1 : Z := i - n in (match r with | Emp => False | Str _ _ _ => False | App f f1 _ => f = right1 ∨ f1 = right1 end) ∧ inv right1 ∧ 0%Z ≤ o1 ∧ o1 < length right1) end) ∧ (∀(result : char), (match r with | Emp => False | Str s ofs _ => result = mixfix_lbrb s (ofs + i) | App left1 right1 _ => (let n : Z := length left1 in if decide (i < n) then result = mixfix_lbrb (string left1) i else result = mixfix_lbrb (string right1) (i - n)) end) -> result = mixfix_lbrb (string r) i).
Admitted.
