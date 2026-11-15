(* Statement-only formalization of PutnamBench artifact putnam_1981_a5:
   distinct real roots of a polynomial expression involving a polynomial and
   its derivative. This file contains no proof. *)

From Stdlib Require Import Reals List ClassicalDescription ClassicalEpsilon.

Import ListNotations.
Open Scope R_scope.

Definition putnam_1981_a5_polynomial : Type := list R.

Fixpoint putnam_1981_a5_eval
    (P : putnam_1981_a5_polynomial) (x : R) : R :=
  match P with
  | [] => 0
  | a :: P' => a + x * putnam_1981_a5_eval P' x
  end.

Fixpoint putnam_1981_a5_add
    (P Q : putnam_1981_a5_polynomial) : putnam_1981_a5_polynomial :=
  match P, Q with
  | [], Q' => Q'
  | P', [] => P'
  | a :: P', b :: Q' => (a + b) :: putnam_1981_a5_add P' Q'
  end.

Definition putnam_1981_a5_scale
    (a : R) (P : putnam_1981_a5_polynomial) :
    putnam_1981_a5_polynomial :=
  map (fun b : R => a * b) P.

Fixpoint putnam_1981_a5_mul
    (P Q : putnam_1981_a5_polynomial) : putnam_1981_a5_polynomial :=
  match P with
  | [] => []
  | a :: P' =>
      putnam_1981_a5_add
        (putnam_1981_a5_scale a Q)
        (0 :: putnam_1981_a5_mul P' Q)
  end.

Fixpoint putnam_1981_a5_derivative_coefficients
    (P : putnam_1981_a5_polynomial) (n : nat) :
    putnam_1981_a5_polynomial :=
  match P with
  | [] => []
  | a :: P' =>
      (INR n * a) ::
      putnam_1981_a5_derivative_coefficients P' (S n)
  end.

Definition putnam_1981_a5_derivative
    (P : putnam_1981_a5_polynomial) : putnam_1981_a5_polynomial :=
  match P with
  | [] => []
  | _ :: P' => putnam_1981_a5_derivative_coefficients P' 1%nat
  end.

Definition putnam_1981_a5_Q
    (P : putnam_1981_a5_polynomial) : putnam_1981_a5_polynomial :=
  let dP := putnam_1981_a5_derivative P in
  putnam_1981_a5_add
    (putnam_1981_a5_mul
      (putnam_1981_a5_mul [1; 0; 1] P) dP)
    (putnam_1981_a5_mul
      [0; 1]
      (putnam_1981_a5_add
        (putnam_1981_a5_mul P P)
        (putnam_1981_a5_mul dP dP))).

Definition putnam_1981_a5_has_cardinality
    (S : R -> Prop) (n : nat) : Prop :=
  exists xs : list R,
    NoDup xs /\
    (forall x : R, In x xs <-> S x) /\
    length xs = n.

Definition putnam_1981_a5_ncard (S : R -> Prop) : nat :=
  match excluded_middle_informative
          (exists n : nat, putnam_1981_a5_has_cardinality S n) with
  | left _ =>
      epsilon (inhabits 0%nat)
        (fun n : nat => putnam_1981_a5_has_cardinality S n)
  | right _ => 0%nat
  end.

Definition putnam_1981_a5_roots_above_one
    (P : putnam_1981_a5_polynomial) : R -> Prop :=
  fun x : R => 1 < x /\ putnam_1981_a5_eval P x = 0.

Definition putnam_1981_a5_roots
    (P : putnam_1981_a5_polynomial) : R -> Prop :=
  fun x : R => putnam_1981_a5_eval P x = 0.

Definition putnam_1981_a5_solution : Prop := True.

Theorem putnam_1981_a5 :
  (forall P : putnam_1981_a5_polynomial,
    INR
      (putnam_1981_a5_ncard
        (putnam_1981_a5_roots (putnam_1981_a5_Q P))) >=
    2 *
      INR
        (putnam_1981_a5_ncard
          (putnam_1981_a5_roots_above_one P)) - 1) <->
  putnam_1981_a5_solution.
Admitted.
