(* Statement-only formalization of VERINA corpus artifact verina_basic_71,
   catalog title "LongestCommonPrefix": executable computation of the longest
   common prefix of two arbitrary Unicode-character lists, together with its
   prefix, maximality, and final correctness contract. This file contains no
   proof. *)

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

Definition lean_char_list_scalar_values
    (chars : list lean_char) : list N :=
  map lean_char_scalar_value chars.

Definition lean_char_option_scalar_value
    (char : option lean_char) : option N :=
  match char with
  | Some c => Some (lean_char_scalar_value c)
  | None => None
  end.

Definition LongestCommonPrefix_precond
    (_str1 _str2 : list lean_char) : Prop :=
  True.

Fixpoint LongestCommonPrefix_aux
    (fuel : nat)
    (str1 str2 : list lean_char)
    (minLength idx : nat)
    (acc : list lean_char) : list lean_char :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Nat.ltb idx minLength
      then
        match nth_error str1 idx, nth_error str2 idx with
        | Some c1, Some c2 =>
            if lean_char_eqb c1 c2
            then
              LongestCommonPrefix_aux
                fuel' str1 str2 minLength (S idx) (acc ++ [c1])
            else acc
        | _, _ => acc
        end
      else acc
  end.

Definition LongestCommonPrefix
    (str1 str2 : list lean_char)
    (_h_precond : LongestCommonPrefix_precond str1 str2) :
    list lean_char :=
  let minLength := Nat.min (length str1) (length str2) in
  LongestCommonPrefix_aux minLength str1 str2 minLength O [].

Definition LongestCommonPrefix_postcond
    (str1 str2 result : list lean_char)
    (_h_precond : LongestCommonPrefix_precond str1 str2) : Prop :=
  (length result <= length str1)%nat /\
  lean_char_list_scalar_values result =
    lean_char_list_scalar_values (firstn (length result) str1) /\
  (length result <= length str2)%nat /\
  lean_char_list_scalar_values result =
    lean_char_list_scalar_values (firstn (length result) str2) /\
  (length result = length str1 \/
   length result = length str2 \/
   lean_char_option_scalar_value
       (nth_error str1 (length result)) <>
     lean_char_option_scalar_value
       (nth_error str2 (length result))).

Theorem LongestCommonPrefix_spec_satisfied
    (str1 str2 : list lean_char)
    (h_precond : LongestCommonPrefix_precond str1 str2) :
  LongestCommonPrefix_postcond
    str1 str2
    (LongestCommonPrefix str1 str2 h_precond)
    h_precond.
Admitted.
