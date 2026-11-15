(* Statement-only formalization of PutnamBench artifact putnam_1989_b6:
   the expected right-endpoint Riemann sum on an ordered simplex is an
   integral against a bounded polynomial of the same dimension. This file
   contains no proof. *)

From Stdlib Require Import Reals RiemannInt.

Open Scope R_scope.

Definition putnam_1989_b6_update
    (x : nat -> R) (i : nat) (y : R) : nat -> R :=
  fun j => if Nat.eq_dec j i then y else x j.

Fixpoint putnam_1989_b6_simplex_integral
    (integral : (R -> R) -> R -> R -> R)
    (remaining index : nat) (lower : R)
    (g : (nat -> R) -> R) (x : nat -> R) : R :=
  match remaining with
  | O => g x
  | S k =>
      integral
        (fun y =>
           putnam_1989_b6_simplex_integral
             integral k (S index) y g
             (putnam_1989_b6_update x index y))
        lower 1
  end.

Definition putnam_1989_b6_uniform_expectation
    (integral : (R -> R) -> R -> R -> R)
    (n : nat) (g : (nat -> R) -> R) : R :=
  putnam_1989_b6_simplex_integral
    integral n 1 0 g (fun _ => 0) /
  putnam_1989_b6_simplex_integral
    integral n 1 0 (fun _ => 1) (fun _ => 0).

Definition putnam_1989_b6_represents_riemann_integral
    (integral : (R -> R) -> R -> R -> R) : Prop :=
  forall (f : R -> R) (a b : R)
         (pr : Riemann_integrable f a b),
    integral f a b = RiemannInt pr.

Definition putnam_1989_b6_extended
    (n : nat) (x : nat -> R) (i : nat) : R :=
  if Nat.eq_dec i O then 0
  else if Nat.eq_dec i (S n) then 1
  else x i.

Definition putnam_1989_b6_sum
    (n : nat) (f : R -> R) (x : nat -> R) : R :=
  sum_f_R0
    (fun i =>
       (putnam_1989_b6_extended n x (S i) -
        putnam_1989_b6_extended n x i) *
       f (putnam_1989_b6_extended n x (S i)))
    n.

Definition putnam_1989_b6_polynomial_value
    (p : nat -> R) (n : nat) (t : R) : R :=
  sum_f_R0 (fun i => p i * t ^ i) n.

Definition putnam_1989_b6_exact_degree
    (p : nat -> R) (n : nat) : Prop :=
  p n <> 0 /\ forall k : nat, (n < k)%nat -> p k = 0.

Definition putnam_1989_b6_continuous_on_unit
    (f : R -> R) : Prop :=
  forall t : R, 0 <= t <= 1 -> continuity_pt f t.

Theorem putnam_1989_b6 :
  forall integral : (R -> R) -> R -> R -> R,
  putnam_1989_b6_represents_riemann_integral integral ->
  forall n : nat, (1 <= n)%nat ->
  exists p : nat -> R,
    putnam_1989_b6_exact_degree p n /\
    (forall t : R, 0 <= t <= 1 ->
       0 <= putnam_1989_b6_polynomial_value p n t <= 1) /\
    (forall f : R -> R,
       f 1 = 0 ->
       putnam_1989_b6_continuous_on_unit f ->
       putnam_1989_b6_uniform_expectation
         integral n (putnam_1989_b6_sum n f) =
       integral
         (fun t => f t * putnam_1989_b6_polynomial_value p n t)
         0 1).
Proof.
Admitted.
