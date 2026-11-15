(*
  Statement-only formalization of Thousand Theorems corpus artifact Q420714
  (thousand-theorems__rocq__Q420714), "Akra-Bazzi theorem": the upper-bound
  part of the theorem for divide-and-conquer recurrences with polynomially
  growing toll functions and asymptotically proportional subproblem sizes.
  This file contains no proof.
*)

From Stdlib Require Import Reals List Arith ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q420714_finite_nonempty_type (A : Type) : Type := {
  q420714_enum : list A;
  q420714_enum_nodup : NoDup q420714_enum;
  q420714_enum_complete :
    forall x : A, In x q420714_enum;
  q420714_inhabitant : A
}.

Arguments q420714_enum {A} _.

Fixpoint q420714_list_sum {A : Type}
    (elements : list A) (f : A -> R) : R :=
  match elements with
  | nil => 0
  | x :: rest => f x + q420714_list_sum rest f
  end.

Definition q420714_finite_sum {A : Type}
    (F : q420714_finite_nonempty_type A)
    (f : A -> R) : R :=
  q420714_list_sum (q420714_enum F) f.

Definition q420714_rpow (x exponent : R) : R :=
  if Req_EM_T x 0
  then if Req_EM_T exponent 0 then 1 else 0
  else Rpower x exponent.

Definition q420714_grows_polynomially (g : R -> R) : Prop :=
  forall beta : R,
    0 < beta < 1 ->
    exists lower_constant : R,
      0 < lower_constant /\
      exists upper_constant : R,
        0 < upper_constant /\
        exists threshold : R,
          forall x : R,
            threshold <= x ->
            forall u : R,
              beta * x <= u <= x ->
              lower_constant * g x <= g u <= upper_constant * g x.

Definition q420714_is_little_o_subproblem_error
    {A : Type}
    (b : A -> R)
    (r : A -> nat -> nat) : Prop :=
  forall i : A,
    forall constant : R,
      0 < constant ->
      exists threshold : nat,
        forall n : nat,
          (threshold <= n)%nat ->
          Rabs (INR (r i n) - b i * INR n) <=
          constant * Rabs (INR n / (ln (INR n)) ^ 2).

Record q420714_akra_bazzi_recurrence
    {A : Type}
    (F : q420714_finite_nonempty_type A)
    (T : nat -> R)
    (g : R -> R)
    (a b : A -> R)
    (r : A -> nat -> nat) : Type := {
  q420714_base_threshold : nat;
  q420714_base_threshold_positive :
    (0 < q420714_base_threshold)%nat;
  q420714_a_positive :
    forall i : A, 0 < a i;
  q420714_b_positive :
    forall i : A, 0 < b i;
  q420714_b_less_than_one :
    forall i : A, b i < 1;
  q420714_g_nonnegative :
    forall x : R, 0 <= x -> 0 <= g x;
  q420714_g_polynomial_growth :
    q420714_grows_polynomially g;
  q420714_recurrence_equation :
    forall n : nat,
      (q420714_base_threshold <= n)%nat ->
      T n =
      q420714_finite_sum F
        (fun i => a i * T (r i n)) +
      g (INR n);
  q420714_base_values_positive :
    forall n : nat,
      (n < q420714_base_threshold)%nat ->
      0 < T n;
  q420714_subproblem_decreases :
    forall (i : A) (n : nat),
      (q420714_base_threshold <= n)%nat ->
      (r i n < n)%nat;
  q420714_subproblem_approximation :
    q420714_is_little_o_subproblem_error b r
}.

Definition q420714_exponent {A : Type}
    (F : q420714_finite_nonempty_type A)
    (a b : A -> R) : R :=
  epsilon (inhabits 0)
    (fun exponent : R =>
      q420714_finite_sum F
        (fun i => a i * q420714_rpow (b i) exponent) = 1).

Fixpoint q420714_partial_sum
    (term : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => q420714_partial_sum term k + term k
  end.

Definition q420714_asymptotic_bound {A : Type}
    (F : q420714_finite_nonempty_type A)
    (g : R -> R)
    (a b : A -> R)
    (n : nat) : R :=
  let exponent := q420714_exponent F a b in
  q420714_rpow (INR n) exponent +
  q420714_rpow (INR n) exponent *
    q420714_partial_sum
      (fun u =>
        g (INR u) /
        q420714_rpow (INR u) (exponent + 1))
      n.

Definition q420714_is_big_o_at_top
    (f h : nat -> R) : Prop :=
  exists constant : R,
    exists threshold : nat,
      forall n : nat,
        (threshold <= n)%nat ->
        Rabs (f n) <= constant * Rabs (h n).

Module AkraBazziRecurrence.

Theorem isBigO_asympBound :
  forall (A : Type)
         (F : q420714_finite_nonempty_type A)
         (T : nat -> R)
         (g : R -> R)
         (a b : A -> R)
         (r : A -> nat -> nat),
    q420714_akra_bazzi_recurrence F T g a b r ->
    q420714_is_big_o_at_top T
      (q420714_asymptotic_bound F g a b).
Admitted.

End AkraBazziRecurrence.
