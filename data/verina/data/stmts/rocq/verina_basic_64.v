(* Statement-only formalization of VERINA corpus artifact verina_basic_64,
   catalog title "insert": executable insertion of a bounded prefix of one
   Unicode-character array into a bounded prefix of another at a specified
   position, together with its precondition, postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import
  Arith.PeanoNat Bool.Bool Lists.List NArith Strings.Ascii.

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

Definition lean_char_eq (x y : lean_char) : Prop :=
  lean_char_scalar_value x = lean_char_scalar_value y.

Definition insert_default_char : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 0).

Definition insert_space_char : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 32).

Definition insert_precond
    (oline : list lean_char)
    (l : nat)
    (nl : list lean_char)
    (p atPos : nat) : Prop :=
  (l <= length oline)%nat /\
  (p <= length nl)%nat /\
  (atPos <= l)%nat.

Fixpoint insert_set_nth
    (index : nat)
    (value : lean_char)
    (xs : list lean_char) : list lean_char :=
  match xs with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' => x :: insert_set_nth index' value rest
      end
  end.

Fixpoint insert_fold_indices
    (count current : nat)
    (step : list lean_char -> nat -> list lean_char)
    (acc : list lean_char) : list lean_char :=
  match count with
  | O => acc
  | S count' =>
      insert_fold_indices
        count' (S current) step (step acc current)
  end.

Definition insert
    (oline : list lean_char)
    (l : nat)
    (nl : list lean_char)
    (p atPos : nat)
    (_h_precond : insert_precond oline l nl p atPos) :
    list lean_char :=
  let result := repeat insert_space_char (l + p)%nat in
  let result :=
    insert_fold_indices
      l O
      (fun (acc : list lean_char) (i : nat) =>
        if Nat.ltb i atPos
        then
          insert_set_nth
            i (nth i oline insert_default_char) acc
        else acc)
      result in
  let result :=
    insert_fold_indices
      p O
      (fun (acc : list lean_char) (i : nat) =>
        insert_set_nth
          (atPos + i)%nat
          (nth i nl insert_default_char)
          acc)
      result in
  insert_fold_indices
    l O
    (fun (acc : list lean_char) (i : nat) =>
      if Nat.leb atPos i
      then
        insert_set_nth
          (i + p)%nat
          (nth i oline insert_default_char)
          acc
      else acc)
    result.

Definition insert_postcond
    (oline : list lean_char)
    (l : nat)
    (nl : list lean_char)
    (p atPos : nat)
    (result : list lean_char)
    (_h_precond : insert_precond oline l nl p atPos) : Prop :=
  length result = (l + p)%nat /\
  (forall i : nat,
      (i < p)%nat ->
      lean_char_eq
        (nth (atPos + i)%nat result insert_default_char)
        (nth i nl insert_default_char)) /\
  (forall i : nat,
      (i < atPos)%nat ->
      lean_char_eq
        (nth i result insert_default_char)
        (nth i oline insert_default_char)) /\
  (forall i : nat,
      (i < l - atPos)%nat ->
      lean_char_eq
        (nth (atPos + p + i)%nat result insert_default_char)
        (nth (atPos + i)%nat oline insert_default_char)).

Theorem insert_spec_satisfied
    (oline : list lean_char)
    (l : nat)
    (nl : list lean_char)
    (p atPos : nat)
    (h_precond : insert_precond oline l nl p atPos) :
  insert_postcond
    oline l nl p atPos
    (insert oline l nl p atPos h_precond)
    h_precond.
Admitted.
