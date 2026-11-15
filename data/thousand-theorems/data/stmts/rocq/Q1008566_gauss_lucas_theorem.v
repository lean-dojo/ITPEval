(*
  Statement-only formalization of Thousand Theorems artifact Q1008566
  (thousand-theorems__rocq__Q1008566), "Gauss–Lucas theorem": roots of the
  derivative of a nonconstant complex polynomial lie in the real convex hull
  of its roots, with the explicit root-multiplicity center-of-mass formula.
  This file contains no proof.
*)

From Stdlib Require Import Reals List Arith.

Import ListNotations.
Open Scope R_scope.

Definition complex := (R * R)%type.
Definition cpolynomial := list complex.

Definition czero : complex := (0, 0).

Definition cadd (z w : complex) : complex :=
  (fst z + fst w, snd z + snd w).

Definition csub (z w : complex) : complex :=
  (fst z - fst w, snd z - snd w).

Definition cmul (z w : complex) : complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition cscale (r : R) (z : complex) : complex :=
  (r * fst z, r * snd z).

Definition cnorm_sq (z : complex) : R :=
  fst z ^ 2 + snd z ^ 2.

Fixpoint poly_eval (p : cpolynomial) (z : complex) : complex :=
  match p with
  | [] => czero
  | a :: q => cadd a (cmul z (poly_eval q z))
  end.

Fixpoint poly_derivative_aux
    (p : cpolynomial) (n : nat) : cpolynomial :=
  match p with
  | [] => []
  | a :: q =>
      cscale (INR n) a :: poly_derivative_aux q (S n)
  end.

Definition poly_derivative (p : cpolynomial) : cpolynomial :=
  match p with
  | [] => []
  | _ :: q => poly_derivative_aux q 1%nat
  end.

Fixpoint iterated_derivative
    (n : nat) (p : cpolynomial) : cpolynomial :=
  match n with
  | O => p
  | S k => poly_derivative (iterated_derivative k p)
  end.

Definition polynomial_positive_degree (p : cpolynomial) : Prop :=
  exists (n : nat) (a : complex),
    (0 < n)%nat /\
    nth_error p n = Some a /\
    a <> czero.

Definition poly_root (p : cpolynomial) (z : complex) : Prop :=
  poly_eval p z = czero.

Definition root_multiplicity
    (p : cpolynomial) (z : complex) (m : nat) : Prop :=
  (forall k : nat,
      (k < m)%nat ->
      poly_root (iterated_derivative k p) z) /\
  ~ poly_root (iterated_derivative m p) z.

Definition root_enumeration
    (p : cpolynomial) (roots : list complex) : Prop :=
  NoDup roots /\
  forall z : complex, In z roots <-> poly_root p z.

Definition deriv_root_weight_spec
    (p : cpolynomial)
    (z : complex)
    (multiplicity : complex -> nat)
    (weight : complex -> R) : Prop :=
  (poly_root p z /\
   weight z = 1 /\
   forall w : complex, w <> z -> weight w = 0) \/
  (~ poly_root p z /\
   forall w : complex,
     weight w =
       INR (multiplicity w) / cnorm_sq (csub z w)).

Fixpoint sum_root_weights
    (roots : list complex) (weight : complex -> R) : R :=
  match roots with
  | [] => 0
  | z :: rest => weight z + sum_root_weights rest weight
  end.

Fixpoint weighted_root_sum
    (roots : list complex) (weight : complex -> R) : complex :=
  match roots with
  | [] => czero
  | z :: rest =>
      cadd (cscale (weight z) z) (weighted_root_sum rest weight)
  end.

Definition center_mass
    (roots : list complex) (weight : complex -> R) : complex :=
  cscale
    (/ sum_root_weights roots weight)
    (weighted_root_sum roots weight).

Fixpoint sum_reals (weights : list R) : R :=
  match weights with
  | [] => 0
  | r :: rest => r + sum_reals rest
  end.

Fixpoint weighted_point_sum
    (points : list complex) (weights : list R) : complex :=
  match points, weights with
  | z :: points', r :: weights' =>
      cadd (cscale r z) (weighted_point_sum points' weights')
  | _, _ => czero
  end.

Definition complex_convex_hull
    (set : complex -> Prop) (z : complex) : Prop :=
  exists (points : list complex) (weights : list R),
    length points = length weights /\
    Forall set points /\
    Forall (fun r : R => 0 <= r) weights /\
    sum_reals weights = 1 /\
    z = weighted_point_sum points weights.

Theorem eq_centerMass_of_eval_derivative_eq_zero :
  forall (p : cpolynomial) (z : complex),
    polynomial_positive_degree p ->
    poly_root (poly_derivative p) z ->
    exists (roots : list complex)
           (multiplicity : complex -> nat)
           (weight : complex -> R),
      root_enumeration p roots /\
      (forall w : complex,
        root_multiplicity p w (multiplicity w)) /\
      deriv_root_weight_spec p z multiplicity weight /\
      z = center_mass roots weight.
Admitted.

Theorem rootSet_derivative_subset_convexHull_rootSet :
  forall p : cpolynomial,
    polynomial_positive_degree p ->
    forall z : complex,
      poly_root (poly_derivative p) z ->
      complex_convex_hull (poly_root p) z.
Admitted.
