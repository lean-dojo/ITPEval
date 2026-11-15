(* Statement-only formalization of VERINA corpus artifact verina_advanced_67,
   catalog title "runLengthEncode": executable run-length encoding of a
   Unicode string into positive character counts with adjacent runs distinct,
   together with the decoding correctness contract. This file contains no
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

Definition lean_string := list lean_char.

Definition lean_char_eqb (x y : lean_char) : bool :=
  match x, y with
  | LeanAscii a, LeanAscii b =>
      Nat.eqb (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
  | LeanNonAscii xcode _ _, LeanNonAscii ycode _ _ =>
      N.eqb xcode ycode
  | _, _ => false
  end.

Definition runLengthEncode_precond (_s : lean_string) : Prop :=
  True.

Fixpoint runLengthEncode_encodeAux
    (acc : list (lean_char * nat))
    (rest : lean_string) : list (lean_char * nat) :=
  match rest with
  | [] => rev acc
  | h :: t =>
      match acc with
      | (ch, count) :: accTail =>
          if lean_char_eqb ch h
          then
            runLengthEncode_encodeAux
              ((ch, S count) :: accTail) t
          else
            runLengthEncode_encodeAux
              ((h, 1%nat) :: (ch, count) :: accTail) t
      | [] =>
          runLengthEncode_encodeAux [(h, 1%nat)] t
      end
  end.

Definition runLengthEncode
    (s : lean_string)
    (_h_precond : runLengthEncode_precond s)
    : list (lean_char * nat) :=
  runLengthEncode_encodeAux [] s.

Fixpoint decodeRLE
    (lst : list (lean_char * nat)) : lean_string :=
  match lst with
  | [] => []
  | (ch, cnt) :: tail =>
      repeat ch cnt ++ decodeRLE tail
  end.

Definition runLengthEncode_default_pair : lean_char * nat :=
  (LeanAscii (Ascii.ascii_of_nat 0), 0%nat).

Definition runLengthEncode_postcond
    (s : lean_string)
    (result : list (lean_char * nat))
    (_h_precond : runLengthEncode_precond s) : Prop :=
  (forall pair, In pair result -> snd pair > 0) /\
  (forall i : nat,
      i < length result - 1 ->
      fst (nth i result runLengthEncode_default_pair) <>
      fst (nth (S i) result runLengthEncode_default_pair)) /\
  decodeRLE result = s.

Theorem runLengthEncode_spec_satisfied
    (s : lean_string)
    (h_precond : runLengthEncode_precond s) :
  runLengthEncode_postcond
    s (runLengthEncode s h_precond) h_precond.
Admitted.
