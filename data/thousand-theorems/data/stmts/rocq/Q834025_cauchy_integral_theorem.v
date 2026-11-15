(*
  Statement-only formalization of Thousand Theorems corpus artifact Q834025
  (thousand-theorems__rocq__Q834025), "Cauchy integral theorem": for a
  complex-valued function continuous on a closed disk and complex
  differentiable on its open disk outside a countable set, the circle
  integral of f(z)/(z-w) is 2*pi*i*f(w) at every interior point w.
  This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalEpsilon RiemannInt.

Set Implicit Arguments.
Local Open Scope R_scope.

Definition q834025_complex : Type := (R * R)%type.
Definition q834025_set (A : Type) : Type := A -> Prop.

Definition q834025_czero : q834025_complex := (0, 0).
Definition q834025_ci : q834025_complex := (0, 1).

Definition q834025_of_real (x : R) : q834025_complex :=
  (x, 0).

Definition q834025_cadd
    (z w : q834025_complex) : q834025_complex :=
  (fst z + fst w, snd z + snd w).

Definition q834025_cneg
    (z : q834025_complex) : q834025_complex :=
  (- fst z, - snd z).

Definition q834025_csub
    (z w : q834025_complex) : q834025_complex :=
  q834025_cadd z (q834025_cneg w).

Definition q834025_cmul
    (z w : q834025_complex) : q834025_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q834025_norm_sq
    (z : q834025_complex) : R :=
  fst z * fst z + snd z * snd z.

Definition q834025_cmodulus
    (z : q834025_complex) : R :=
  sqrt (q834025_norm_sq z).

Definition q834025_cinv
    (z : q834025_complex) : q834025_complex :=
  if Req_EM_T (q834025_norm_sq z) 0 then
    q834025_czero
  else
    (fst z / q834025_norm_sq z,
     - snd z / q834025_norm_sq z).

Definition q834025_cdiv
    (z w : q834025_complex) : q834025_complex :=
  q834025_cmul z (q834025_cinv w).

Definition q834025_open_ball
    (center : q834025_complex) (radius : R) :
    q834025_set q834025_complex :=
  fun z =>
    q834025_cmodulus (q834025_csub z center) < radius.

Definition q834025_closed_ball
    (center : q834025_complex) (radius : R) :
    q834025_set q834025_complex :=
  fun z =>
    q834025_cmodulus (q834025_csub z center) <= radius.

Definition q834025_countable
    {A : Type} (S : q834025_set A) : Prop :=
  exists encode : A -> nat,
    forall x y : A,
      S x ->
      S y ->
      encode x = encode y ->
      x = y.

Definition q834025_continuous_within_at
    (f : q834025_complex -> q834025_complex)
    (S : q834025_set q834025_complex)
    (z : q834025_complex) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : q834025_complex,
        S w ->
        q834025_cmodulus (q834025_csub w z) < delta ->
        q834025_cmodulus
          (q834025_csub (f w) (f z)) < epsilon.

Definition q834025_continuous_on
    (f : q834025_complex -> q834025_complex)
    (S : q834025_set q834025_complex) : Prop :=
  forall z : q834025_complex,
    S z -> q834025_continuous_within_at f S z.

Definition q834025_has_complex_derivative_at
    (f : q834025_complex -> q834025_complex)
    (z derivative : q834025_complex) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall h : q834025_complex,
        q834025_cmodulus h < delta ->
        q834025_cmodulus
          (q834025_csub
            (q834025_csub
              (f (q834025_cadd z h)) (f z))
            (q834025_cmul derivative h))
        <= epsilon * q834025_cmodulus h.

Definition q834025_complex_differentiable_at
    (f : q834025_complex -> q834025_complex)
    (z : q834025_complex) : Prop :=
  exists derivative : q834025_complex,
    q834025_has_complex_derivative_at f z derivative.

Definition q834025_circle_map
    (center : q834025_complex) (radius theta : R) :
    q834025_complex :=
  q834025_cadd center
    (radius * cos theta, radius * sin theta).

Definition q834025_circle_map_derivative
    (radius theta : R) : q834025_complex :=
  (- radius * sin theta, radius * cos theta).

Definition q834025_real_integral
    (g : R -> R) (a b : R) : R :=
  epsilon (inhabits 0)
    (fun value : R =>
      exists integrable : Riemann_integrable g a b,
        value = RiemannInt integrable).

Definition q834025_complex_integral
    (g : R -> q834025_complex) (a b : R) :
    q834025_complex :=
  (q834025_real_integral (fun theta => fst (g theta)) a b,
   q834025_real_integral (fun theta => snd (g theta)) a b).

Definition q834025_circle_integral
    (g : q834025_complex -> q834025_complex)
    (center : q834025_complex) (radius : R) :
    q834025_complex :=
  q834025_complex_integral
    (fun theta =>
      q834025_cmul
        (q834025_circle_map_derivative radius theta)
        (g (q834025_circle_map center radius theta)))
    0 (2 * PI).

Theorem Complex_circleIntegral_div_sub_of_differentiable_on_off_countable :
  forall (R0 : R)
         (c w : q834025_complex)
         (s : q834025_set q834025_complex)
         (f : q834025_complex -> q834025_complex),
    q834025_countable s ->
    q834025_open_ball c R0 w ->
    q834025_continuous_on f (q834025_closed_ball c R0) ->
    (forall z : q834025_complex,
      q834025_open_ball c R0 z ->
      ~ s z ->
      q834025_complex_differentiable_at f z) ->
    q834025_circle_integral
      (fun z => q834025_cdiv (f z) (q834025_csub z w))
      c R0 =
    q834025_cmul
      (q834025_cmul (q834025_of_real (2 * PI)) q834025_ci)
      (f w).
Admitted.
