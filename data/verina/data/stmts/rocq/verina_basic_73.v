(* Statement-only formalization of VERINA corpus artifact verina_basic_73,
   catalog title "Match": an executable left-to-right wildcard match of two
   equal-length arbitrary Unicode strings, accepting when each pattern
   character is equal to the corresponding source character or is `?`,
   together with its correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List NArith Strings.Ascii.

Import ListNotations.

Definition unicode_scalar (code : N) : Prop :=
  (code < 55296)%N \/
  ((57343 < code)%N /\ (code < 1114112)%N).

Inductive lean_char : Type :=
| LeanAscii : ascii -> lean_char
| LeanNonAscii :
    forall code : N,
      (256 <= code)%N ->
      unicode_scalar code ->
      lean_char.

Definition lean_char_scalar_value (c : lean_char) : N :=
  match c with
  | LeanAscii a => N.of_nat (Ascii.nat_of_ascii a)
  | LeanNonAscii code _ _ => code
  end.

Definition lean_char_eqb (x y : lean_char) : bool :=
  N.eqb (lean_char_scalar_value x) (lean_char_scalar_value y).

Definition lean_string := list lean_char.

Definition Match_question_mark : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 63).

Definition Match_default_char : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 0).

Definition Match_precond (s p : lean_string) : Prop :=
  length s = length p.

Fixpoint Match_loop (sList pList : lean_string) : bool :=
  match sList, pList with
  | [], [] => true
  | sChar :: sRest, pChar :: pRest =>
      if andb
           (negb (lean_char_eqb sChar pChar))
           (negb (lean_char_eqb pChar Match_question_mark))
      then false
      else Match_loop sRest pRest
  | _, _ => false
  end.

Definition Match
    (s p : lean_string)
    (_h_precond : Match_precond s p) : bool :=
  Match_loop s p.

Definition Match_postcond
    (s p : lean_string)
    (result : bool)
    (_h_precond : Match_precond s p) : Prop :=
  result = true <->
  forall n : nat,
    (n < length s)%nat ->
    lean_char_scalar_value (nth n s Match_default_char) =
      lean_char_scalar_value (nth n p Match_default_char) \/
    lean_char_scalar_value (nth n p Match_default_char) =
      lean_char_scalar_value Match_question_mark.

Theorem Match_spec_satisfied
    (s p : lean_string)
    (h_precond : Match_precond s p) :
  Match_postcond s p (Match s p h_precond) h_precond.
Admitted.
