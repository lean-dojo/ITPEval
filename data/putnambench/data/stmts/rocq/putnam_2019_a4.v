(* Statement-only formalization of PutnamBench corpus artifact putnam_2019_a4:
   whether a continuous real-valued function on R^3 whose surface integral
   over every unit sphere is zero must be identically zero; the answer is
   false. This file contains no proof. *)

From Stdlib Require Import Reals RiemannInt.

Local Open Scope R_scope.

Definition putnam_2019_a4_point : Type := (R * (R * R))%type.

Definition putnam_2019_a4_x (p : putnam_2019_a4_point) : R :=
  fst p.

Definition putnam_2019_a4_y (p : putnam_2019_a4_point) : R :=
  fst (snd p).

Definition putnam_2019_a4_z (p : putnam_2019_a4_point) : R :=
  snd (snd p).

Definition putnam_2019_a4_distance
    (p q : putnam_2019_a4_point) : R :=
  sqrt
    ((putnam_2019_a4_x p - putnam_2019_a4_x q) ^ 2 +
     (putnam_2019_a4_y p - putnam_2019_a4_y q) ^ 2 +
     (putnam_2019_a4_z p - putnam_2019_a4_z q) ^ 2).

Definition putnam_2019_a4_continuous
    (f : putnam_2019_a4_point -> R) : Prop :=
  forall p : putnam_2019_a4_point,
    forall epsilon : R,
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall q : putnam_2019_a4_point,
          putnam_2019_a4_distance q p < delta ->
          Rabs (f q - f p) < epsilon.

Definition putnam_2019_a4_unit_sphere_parameter
    (center : putnam_2019_a4_point)
    (theta phi : R) : putnam_2019_a4_point :=
  (putnam_2019_a4_x center + sin phi * cos theta,
   (putnam_2019_a4_y center + sin phi * sin theta,
    putnam_2019_a4_z center + cos phi)).

Definition putnam_2019_a4_surface_integrand
    (f : putnam_2019_a4_point -> R)
    (center : putnam_2019_a4_point)
    (theta phi : R) : R :=
  f (putnam_2019_a4_unit_sphere_parameter center theta phi) * sin phi.

(* This is the standard spherical-coordinate surface integral on the unit
   sphere centered at [center], with area element sin(phi) dphi dtheta. *)
Definition putnam_2019_a4_unit_sphere_integral_has_value
    (f : putnam_2019_a4_point -> R)
    (center : putnam_2019_a4_point)
    (value : R) : Prop :=
  exists inner_integrable :
      forall theta : R,
        Riemann_integrable
          (fun phi =>
             putnam_2019_a4_surface_integrand f center theta phi)
          0 PI,
    exists outer_integrable :
      Riemann_integrable
        (fun theta => RiemannInt (inner_integrable theta))
        0 (2 * PI),
      RiemannInt outer_integrable = value.

Theorem putnam_2019_a4 :
  (forall f : putnam_2019_a4_point -> R,
      putnam_2019_a4_continuous f ->
      (forall center : putnam_2019_a4_point,
          putnam_2019_a4_unit_sphere_integral_has_value f center 0) ->
      forall p : putnam_2019_a4_point, f p = 0) <->
  False.
Admitted.
