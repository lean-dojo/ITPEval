(* Statement-only formalization of VERINA corpus artifact verina_basic_108,
   catalog title "below_zero": an executable construction of integer prefix
   sums and a Boolean check for a negative prefix, together with its
   precondition, postcondition, and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition below_zero_precond
    (_operations : list Z) : Prop :=
  True.

Definition buildS_step
    (acc : list Z)
    (op : Z) : list Z :=
  acc ++ [last acc 0%Z + op].

Definition buildS
    (operations : list Z) : list Z :=
  fold_left buildS_step operations [0%Z].

Fixpoint below_zero_check_negative
    (values : list Z) : bool :=
  match values with
  | [] => false
  | x :: xs =>
      if Z.ltb x 0%Z
      then true
      else below_zero_check_negative xs
  end.

Definition below_zero
    (operations : list Z)
    (_h_precond : below_zero_precond operations)
    : (list Z * bool)%type :=
  let s := buildS operations in
  (s, below_zero_check_negative s).

Definition below_zero_option_Z_eqb
    (x y : option Z) : bool :=
  match x, y with
  | Some a, Some b => Z.eqb a b
  | None, None => true
  | _, _ => false
  end.

Definition below_zero_postcond
    (operations : list Z)
    (result : (list Z * bool)%type)
    (_h_precond : below_zero_precond operations) : Prop :=
  let s := fst result in
  let outcome := snd result in
  length s = (length operations + 1)%nat /\
  nth_error s 0%nat = Some 0%Z /\
  forallb
    (fun i =>
      below_zero_option_Z_eqb
        (nth_error s (S i))
        (Some (nth i s 0%Z + nth i operations 0%Z)))
    (seq 0%nat (length s - 1)%nat) = true /\
  (outcome = true ->
    existsb
      (fun i => Z.ltb (nth (S i) s 0%Z) 0%Z)
      (seq 0%nat (length operations)) = true) /\
  (outcome = false ->
    forallb (fun x => Z.leb 0%Z x) s = true).

Theorem below_zero_spec_satisfied
    (operations : list Z)
    (h_precond : below_zero_precond operations) :
  below_zero_postcond
    operations (below_zero operations h_precond) h_precond.
Admitted.
