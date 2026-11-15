(*
  Statement-only formalization of Thousand Theorems corpus artifact Q530152
  (thousand-theorems__rocq__Q530152), "Picard&ndash;Lindelöf theorem":
  local existence for a time-dependent Lipschitz vector field on a real
  Banach space, with a prescribed initial value. This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Local Open Scope R_scope.

Definition q530152_set (A : Type) : Type := A -> Prop.

Record q530152_normed_real_vector_space (E : Type) : Type := {
  q530152_zero : E;
  q530152_add : E -> E -> E;
  q530152_neg : E -> E;
  q530152_smul : R -> E -> E;
  q530152_norm : E -> R;
  q530152_add_assoc :
    forall x y z : E,
      q530152_add x (q530152_add y z) =
      q530152_add (q530152_add x y) z;
  q530152_add_comm :
    forall x y : E, q530152_add x y = q530152_add y x;
  q530152_add_zero :
    forall x : E, q530152_add x q530152_zero = x;
  q530152_add_neg :
    forall x : E,
      q530152_add x (q530152_neg x) = q530152_zero;
  q530152_one_smul :
    forall x : E, q530152_smul 1 x = x;
  q530152_mul_smul :
    forall (a b : R) (x : E),
      q530152_smul (a * b) x =
      q530152_smul a (q530152_smul b x);
  q530152_add_smul :
    forall (a b : R) (x : E),
      q530152_smul (a + b) x =
      q530152_add (q530152_smul a x) (q530152_smul b x);
  q530152_smul_add :
    forall (a : R) (x y : E),
      q530152_smul a (q530152_add x y) =
      q530152_add (q530152_smul a x) (q530152_smul a y);
  q530152_zero_smul :
    forall x : E, q530152_smul 0 x = q530152_zero;
  q530152_smul_zero :
    forall a : R, q530152_smul a q530152_zero = q530152_zero;
  q530152_norm_nonnegative :
    forall x : E, 0 <= q530152_norm x;
  q530152_norm_eq_zero :
    forall x : E, q530152_norm x = 0 <-> x = q530152_zero;
  q530152_norm_add_le :
    forall x y : E,
      q530152_norm (q530152_add x y) <=
      q530152_norm x + q530152_norm y;
  q530152_norm_smul :
    forall (a : R) (x : E),
      q530152_norm (q530152_smul a x) =
      Rabs a * q530152_norm x
}.

Arguments q530152_zero {E} _.
Arguments q530152_add {E} _ _ _.
Arguments q530152_neg {E} _ _.
Arguments q530152_smul {E} _ _ _.
Arguments q530152_norm {E} _ _.

Definition q530152_sub
    {E : Type}
    (V : q530152_normed_real_vector_space E)
    (x y : E) : E :=
  q530152_add V x (q530152_neg V y).

Definition q530152_sequence_converges
    {E : Type}
    (V : q530152_normed_real_vector_space E)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q530152_norm V (q530152_sub V (u n) limit) < epsilon.

Definition q530152_sequence_cauchy
    {E : Type}
    (V : q530152_normed_real_vector_space E)
    (u : nat -> E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q530152_norm V (q530152_sub V (u m) (u n)) < epsilon.

Definition q530152_complete
    {E : Type}
    (V : q530152_normed_real_vector_space E) : Prop :=
  forall u : nat -> E,
    q530152_sequence_cauchy V u ->
    exists limit : E,
      q530152_sequence_converges V u limit.

Definition q530152_Icc (lower upper : R) : q530152_set R :=
  fun t : R => lower <= t /\ t <= upper.

Definition q530152_closed_ball
    {E : Type}
    (V : q530152_normed_real_vector_space E)
    (center : E) (radius : R) : q530152_set E :=
  fun x : E => q530152_norm V (q530152_sub V x center) <= radius.

Definition q530152_lipschitz_on_with
    {E : Type}
    (V : q530152_normed_real_vector_space E)
    (constant : R) (g : E -> E) (S : q530152_set E) : Prop :=
  forall x y : E,
    S x ->
    S y ->
    q530152_norm V (q530152_sub V (g x) (g y)) <=
      constant * q530152_norm V (q530152_sub V x y).

Definition q530152_continuous_on
    {E : Type}
    (V : q530152_normed_real_vector_space E)
    (g : R -> E) (S : q530152_set R) : Prop :=
  forall t : R,
    S t ->
    forall epsilon : R,
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall u : R,
          S u ->
          Rabs (u - t) < delta ->
          q530152_norm V (q530152_sub V (g u) (g t)) < epsilon.

Definition q530152_has_deriv_within_at
    {E : Type}
    (V : q530152_normed_real_vector_space E)
    (alpha : R -> E) (derivative : E)
    (S : q530152_set R) (t : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall u : R,
        S u ->
        Rabs (u - t) < delta ->
        q530152_norm V
          (q530152_sub V
            (q530152_sub V (alpha u) (alpha t))
            (q530152_smul V (u - t) derivative)) <=
          epsilon * Rabs (u - t).

Record q530152_is_picard_lindelof
    (E : Type)
    (V : q530152_normed_real_vector_space E)
    (f : R -> E -> E)
    (tmin tmax t0 : R)
    (x0 : E)
    (a r L K : R) : Prop := {
  q530152_a_nonnegative : 0 <= a;
  q530152_r_nonnegative : 0 <= r;
  q530152_L_nonnegative : 0 <= L;
  q530152_K_nonnegative : 0 <= K;
  q530152_t0_mem : q530152_Icc tmin tmax t0;
  q530152_lipschitz :
    forall t : R,
      q530152_Icc tmin tmax t ->
      q530152_lipschitz_on_with V K (f t)
        (q530152_closed_ball V x0 a);
  q530152_continuous :
    forall y : E,
      q530152_closed_ball V x0 a y ->
      q530152_continuous_on V
        (fun t : R => f t y) (q530152_Icc tmin tmax);
  q530152_norm_le :
    forall t : R,
      q530152_Icc tmin tmax t ->
      forall y : E,
        q530152_closed_ball V x0 a y ->
        q530152_norm V (f t y) <= L;
  q530152_time_bound :
    L * Rmax (tmax - t0) (t0 - tmin) <= a - r
}.

Theorem IsPicardLindelof_exists_eq_forall_mem_Icc_hasDerivWithinAt :
  forall
    (E : Type)
    (V : q530152_normed_real_vector_space E),
    q530152_complete V ->
    forall
      (f : R -> E -> E)
      (tmin tmax t0 : R)
      (x0 x : E)
      (a r L K : R),
      q530152_is_picard_lindelof
        E V f tmin tmax t0 x0 a r L K ->
      q530152_closed_ball V x0 r x ->
      exists alpha : R -> E,
        alpha t0 = x /\
        forall t : R,
          q530152_Icc tmin tmax t ->
          q530152_has_deriv_within_at V
            alpha (f t (alpha t)) (q530152_Icc tmin tmax) t.
Admitted.
