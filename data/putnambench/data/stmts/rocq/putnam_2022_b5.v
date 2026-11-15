(* Statement-only formalization of PutnamBench corpus artifact putnam_2022_b5:
   the parameters for which zero is a most likely value of every finite
   integer-weighted sum of independent {-1, 0, 1}-valued variables are exactly
   the real interval [0, 1/4]. This file contains no proof. *)

From Stdlib Require Import Reals ZArith Lists.List.

Import ListNotations.
Open Scope R_scope.

Fixpoint putnam_2022_b5_weighted_sum_probability
    (p : R)
    (coefficients : list Z)
    (target : Z) : R :=
  match coefficients with
  | [] =>
      if Z.eq_dec target 0%Z then 1 else 0
  | coefficient :: rest =>
      p *
        putnam_2022_b5_weighted_sum_probability
          p rest (target - coefficient)%Z
      + (1 - 2 * p) *
        putnam_2022_b5_weighted_sum_probability
          p rest target
      + p *
        putnam_2022_b5_weighted_sum_probability
          p rest (target + coefficient)%Z
  end.

Definition putnam_2022_b5_zero_is_most_likely
    (p : R) : Prop :=
  forall (n : nat) (coefficients : list Z),
    (0 < n)%nat ->
    length coefficients = n ->
    forall target : Z,
      putnam_2022_b5_weighted_sum_probability
        p coefficients 0%Z
      >=
      putnam_2022_b5_weighted_sum_probability
        p coefficients target.

Definition putnam_2022_b5_solution
    (p : R) : Prop :=
  0 <= p /\ p <= 1 / 4.

Theorem putnam_2022_b5 :
  forall p : R,
    (0 <= p /\
     p <= 1 / 2 /\
     putnam_2022_b5_zero_is_most_likely p) <->
    putnam_2022_b5_solution p.
Admitted.
