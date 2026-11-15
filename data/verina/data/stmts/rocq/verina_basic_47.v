(* Statement-only formalization of VERINA corpus artifact verina_basic_47,
   catalog title "arraySum": an executable sum of all elements of a nonempty
   integer array, together with its recursive indexed-sum postcondition and
   final correctness proposition. This file contains no proof. *)

From Stdlib Require Import Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition arraySum_precond (a : list Z) : Prop :=
  (0 < length a)%nat.

Fixpoint arraySum_list_sum (a : list Z) : Z :=
  match a with
  | [] => 0
  | x :: xs => x + arraySum_list_sum xs
  end.

Definition arraySum
    (a : list Z)
    (_h_precond : arraySum_precond a) : Z :=
  arraySum_list_sum a.

Fixpoint sumTo (a : list Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => sumTo a k + nth k a 0
  end.

Definition arraySum_postcond
    (a : list Z)
    (result : Z)
    (_h_precond : arraySum_precond a) : Prop :=
  result - sumTo a (length a) = 0 /\
  result >= sumTo a (length a).

Theorem arraySum_spec_satisfied
    (a : list Z)
    (h_precond : arraySum_precond a) :
  arraySum_postcond a (arraySum a h_precond) h_precond.
Admitted.
