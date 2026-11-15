(* Statement-only formalization of PutnamBench corpus artifact putnam_2021_b3:
   every twice continuously differentiable real function on the plane has,
   for each pair of parameters 0 < r < d, a disk of radius r centered at distance
   d from the origin on which the integral of y h_x - x h_y is zero; the
   assertion is true. This file contains no proof. *)

From Stdlib Require Import Reals ClassicalEpsilon RiemannInt.

Open Scope R_scope.

Definition putnam_2021_b3_point : Type := (R * R)%type.

Definition putnam_2021_b3_real_derivative
    (f : R -> R) (x : R) : R :=
  epsilon (inhabits (0 : R))
    (fun derivative : R => derivable_pt_lim f x derivative).

Definition putnam_2021_b3_partial_x
    (h : putnam_2021_b3_point -> R)
    (p : putnam_2021_b3_point) : R :=
  putnam_2021_b3_real_derivative
    (fun x : R => h (x, snd p))
    (fst p).

Definition putnam_2021_b3_partial_y
    (h : putnam_2021_b3_point -> R)
    (p : putnam_2021_b3_point) : R :=
  putnam_2021_b3_real_derivative
    (fun y : R => h (fst p, y))
    (snd p).

Definition putnam_2021_b3_partial_xx
    (h : putnam_2021_b3_point -> R)
    (p : putnam_2021_b3_point) : R :=
  putnam_2021_b3_real_derivative
    (fun x : R => putnam_2021_b3_partial_x h (x, snd p))
    (fst p).

Definition putnam_2021_b3_partial_xy
    (h : putnam_2021_b3_point -> R)
    (p : putnam_2021_b3_point) : R :=
  putnam_2021_b3_real_derivative
    (fun y : R => putnam_2021_b3_partial_x h (fst p, y))
    (snd p).

Definition putnam_2021_b3_partial_yx
    (h : putnam_2021_b3_point -> R)
    (p : putnam_2021_b3_point) : R :=
  putnam_2021_b3_real_derivative
    (fun x : R => putnam_2021_b3_partial_y h (x, snd p))
    (fst p).

Definition putnam_2021_b3_partial_yy
    (h : putnam_2021_b3_point -> R)
    (p : putnam_2021_b3_point) : R :=
  putnam_2021_b3_real_derivative
    (fun y : R => putnam_2021_b3_partial_y h (fst p, y))
    (snd p).

Definition putnam_2021_b3_continuous_plane
    (f : putnam_2021_b3_point -> R) : Prop :=
  forall p : putnam_2021_b3_point,
    forall eps : R,
      eps > 0 ->
      exists delta : R,
        delta > 0 /\
        forall q : putnam_2021_b3_point,
          Rabs (fst q - fst p) < delta ->
          Rabs (snd q - snd p) < delta ->
          Rabs (f q - f p) < eps.

Definition putnam_2021_b3_contdiff_two
    (h : putnam_2021_b3_point -> R) : Prop :=
  (forall p : putnam_2021_b3_point,
    derivable_pt_lim
      (fun x : R => h (x, snd p))
      (fst p)
      (putnam_2021_b3_partial_x h p) /\
    derivable_pt_lim
      (fun y : R => h (fst p, y))
      (snd p)
      (putnam_2021_b3_partial_y h p) /\
    derivable_pt_lim
      (fun x : R => putnam_2021_b3_partial_x h (x, snd p))
      (fst p)
      (putnam_2021_b3_partial_xx h p) /\
    derivable_pt_lim
      (fun y : R => putnam_2021_b3_partial_x h (fst p, y))
      (snd p)
      (putnam_2021_b3_partial_xy h p) /\
    derivable_pt_lim
      (fun x : R => putnam_2021_b3_partial_y h (x, snd p))
      (fst p)
      (putnam_2021_b3_partial_yx h p) /\
    derivable_pt_lim
      (fun y : R => putnam_2021_b3_partial_y h (fst p, y))
      (snd p)
      (putnam_2021_b3_partial_yy h p)) /\
  putnam_2021_b3_continuous_plane h /\
  putnam_2021_b3_continuous_plane
    (putnam_2021_b3_partial_x h) /\
  putnam_2021_b3_continuous_plane
    (putnam_2021_b3_partial_y h) /\
  putnam_2021_b3_continuous_plane
    (putnam_2021_b3_partial_xx h) /\
  putnam_2021_b3_continuous_plane
    (putnam_2021_b3_partial_xy h) /\
  putnam_2021_b3_continuous_plane
    (putnam_2021_b3_partial_yx h) /\
  putnam_2021_b3_continuous_plane
    (putnam_2021_b3_partial_yy h).

Definition putnam_2021_b3_rho
    (h : putnam_2021_b3_point -> R)
    (p : putnam_2021_b3_point) : R :=
  snd p * putnam_2021_b3_partial_x h p -
  fst p * putnam_2021_b3_partial_y h p.

Definition putnam_2021_b3_distance
    (p q : putnam_2021_b3_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_2021_b3_disk_integral_has_value
    (f : putnam_2021_b3_point -> R)
    (center : putnam_2021_b3_point)
    (radius value : R) : Prop :=
  exists inner_integral : R -> R,
    (forall x : R,
      fst center - radius <= x <= fst center + radius ->
      exists inner_integrable :
        Riemann_integrable
          (fun y : R => f (x, y))
          (snd center -
            sqrt (radius ^ 2 - (x - fst center) ^ 2))
          (snd center +
            sqrt (radius ^ 2 - (x - fst center) ^ 2)),
        inner_integral x = RiemannInt inner_integrable) /\
    exists outer_integrable :
      Riemann_integrable
        inner_integral
        (fst center - radius)
        (fst center + radius),
      value = RiemannInt outer_integrable.

Definition putnam_2021_b3_solution : Prop := True.

Theorem putnam_2021_b3 :
  ((forall h : putnam_2021_b3_point -> R,
      putnam_2021_b3_contdiff_two h ->
      forall d r : R,
        0 < d ->
        0 < r ->
        d > r ->
        exists center : putnam_2021_b3_point,
          putnam_2021_b3_distance center (0, 0) = d /\
          putnam_2021_b3_disk_integral_has_value
            (putnam_2021_b3_rho h)
            center
            r
            0) <->
    putnam_2021_b3_solution).
Admitted.
