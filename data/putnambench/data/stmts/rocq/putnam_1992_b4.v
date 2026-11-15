(* Statement-only formalization of PutnamBench corpus artifact putnam_1992_b4:
   the least numerator degree after differentiating p(x)/(x^3-x) 1992 times,
   for nonzero p of degree below 1992 coprime to x^3-x, is 3984. This file
   contains no proof. *)

From Coq Require Import Reals ClassicalEpsilon ClassicalDescription.

Open Scope R_scope.

Record putnam_1992_b4_polynomial : Type := {
  putnam_1992_b4_coeff : nat -> R;
  putnam_1992_b4_bound : nat;
  putnam_1992_b4_finite :
    forall n : nat,
      (putnam_1992_b4_bound < n)%nat ->
      putnam_1992_b4_coeff n = 0
}.

Definition putnam_1992_b4_eval
    (p : putnam_1992_b4_polynomial) (x : R) : R :=
  sum_f_R0
    (fun n : nat => putnam_1992_b4_coeff p n * x ^ n)
    (putnam_1992_b4_bound p).

Definition putnam_1992_b4_zero
    (p : putnam_1992_b4_polynomial) : Prop :=
  forall n : nat, putnam_1992_b4_coeff p n = 0.

Definition putnam_1992_b4_degree
    (p : putnam_1992_b4_polynomial) (d : nat) : Prop :=
  (putnam_1992_b4_zero p /\ d = 0%nat) \/
  (putnam_1992_b4_coeff p d <> 0 /\
   forall n : nat,
     (d < n)%nat ->
     putnam_1992_b4_coeff p n = 0).

Definition putnam_1992_b4_product_coeff
    (p q : putnam_1992_b4_polynomial) (n : nat) : R :=
  sum_f_R0
    (fun k : nat =>
       putnam_1992_b4_coeff p k *
       putnam_1992_b4_coeff q (n - k)%nat)
    n.

Definition putnam_1992_b4_divides
    (d p : putnam_1992_b4_polynomial) : Prop :=
  exists q : putnam_1992_b4_polynomial,
    forall n : nat,
      putnam_1992_b4_coeff p n =
      putnam_1992_b4_product_coeff d q n.

Definition putnam_1992_b4_x3_minus_x_coeff (n : nat) : R :=
  match n with
  | 1%nat => -1
  | 3%nat => 1
  | _ => 0
  end.

Definition putnam_1992_b4_divides_x3_minus_x
    (d : putnam_1992_b4_polynomial) : Prop :=
  exists q : putnam_1992_b4_polynomial,
    forall n : nat,
      putnam_1992_b4_x3_minus_x_coeff n =
      putnam_1992_b4_product_coeff d q n.

Definition putnam_1992_b4_constant
    (p : putnam_1992_b4_polynomial) : Prop :=
  forall n : nat,
    (0 < n)%nat ->
    putnam_1992_b4_coeff p n = 0.

Definition putnam_1992_b4_coprime_x3_minus_x
    (p : putnam_1992_b4_polynomial) : Prop :=
  forall d : putnam_1992_b4_polynomial,
    putnam_1992_b4_divides d p ->
    putnam_1992_b4_divides_x3_minus_x d ->
    putnam_1992_b4_constant d.

Definition putnam_1992_b4_total_derivative
    (f : R -> R) (x : R) : R :=
  match excluded_middle_informative
          (exists d : R, derivable_pt_lim f x d) with
  | left _ =>
      epsilon (inhabits (0 : R))
        (fun d : R => derivable_pt_lim f x d)
  | right _ => 0
  end.

Fixpoint putnam_1992_b4_iterated_derivative
    (n : nat) (f : R -> R) : R -> R :=
  match n with
  | O => f
  | S k =>
      fun x : R =>
        putnam_1992_b4_total_derivative
          (putnam_1992_b4_iterated_derivative k f) x
  end.

Definition putnam_1992_b4_valid
    (p : putnam_1992_b4_polynomial) : Prop :=
  ~ putnam_1992_b4_zero p /\
  (exists d : nat,
      putnam_1992_b4_degree p d /\
      (d < 1992)%nat) /\
  putnam_1992_b4_coprime_x3_minus_x p.

Definition putnam_1992_b4_pair
    (p f : putnam_1992_b4_polynomial) : Prop :=
  exists g : putnam_1992_b4_polynomial,
    ~ putnam_1992_b4_zero g /\
    forall x : R,
      x <> -1 ->
      x <> 0 ->
      x <> 1 ->
      putnam_1992_b4_eval g x <> 0 ->
      putnam_1992_b4_iterated_derivative 1992
        (fun y : R =>
           putnam_1992_b4_eval p y / (y ^ 3 - y)) x =
      putnam_1992_b4_eval f x / putnam_1992_b4_eval g x.

Definition putnam_1992_b4_solution : nat := 3984%nat.

Theorem putnam_1992_b4 :
  (exists p f : putnam_1992_b4_polynomial,
      putnam_1992_b4_valid p /\
      putnam_1992_b4_pair p f /\
      putnam_1992_b4_degree f putnam_1992_b4_solution) /\
  (forall (p f : putnam_1992_b4_polynomial) (d : nat),
      putnam_1992_b4_valid p ->
      putnam_1992_b4_pair p f ->
      putnam_1992_b4_degree f d ->
      (putnam_1992_b4_solution <= d)%nat).
Admitted.
