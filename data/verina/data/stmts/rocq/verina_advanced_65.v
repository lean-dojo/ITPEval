(* Statement-only formalization of VERINA corpus artifact verina_advanced_65,
   catalog title "reverseString": executable accumulator-based reversal of an
   arbitrary Unicode string, together with length preservation and exact
   reversed-character correctness. This file contains no proof. *)

From Stdlib Require Import Lists.List NArith Strings.Ascii.

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

Definition lean_string := list lean_char.

Definition reverseString_precond (_s : lean_string) : Prop :=
  True.

Fixpoint reverseAux
    (chars acc : list lean_char) : list lean_char :=
  match chars with
  | [] => acc
  | head :: tail => reverseAux tail (head :: acc)
  end.

Definition reverseString
    (s : lean_string)
    (_h_precond : reverseString_precond s) : lean_string :=
  reverseAux s [].

Definition reverseString_postcond
    (s result : lean_string)
    (_h_precond : reverseString_precond s) : Prop :=
  length result = length s /\
  result = rev s.

Theorem reverseString_spec_satisfied
    (s : lean_string)
    (h_precond : reverseString_precond s) :
  reverseString_postcond
    s (reverseString s h_precond) h_precond.
Admitted.
