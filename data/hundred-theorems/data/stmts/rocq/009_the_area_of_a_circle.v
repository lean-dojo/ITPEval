(*
  Statement-only formalization of "The Area of a Circle" from Hundred Theorems item 009. This
  file contains no proof.
*)

From Stdlib Require Import Reals RiemannInt.

#[local] Open Scope R_scope.

Definition open_disc
    (center : (R * R)%type) (radius : R) : (R * R)%type -> Prop :=
  fun p =>
    (fst p - fst center) ^ 2 + (snd p - snd center) ^ 2 < radius ^ 2.

Definition disc_indicator
    (center : (R * R)%type) (radius : R) (p : (R * R)%type) : R :=
  if Rlt_dec
       ((fst p - fst center) ^ 2 + (snd p - snd center) ^ 2)
       (radius ^ 2)
  then 1
  else 0.

Definition iterated_Riemann_integral
    (f : R -> R -> R) (x0 x1 y0 y1 value : R) : Prop :=
  exists inner_integrable :
      forall x : R, Riemann_integrable (fun y => f x y) y0 y1,
    exists outer_integrable :
      Riemann_integrable
        (fun x => RiemannInt (inner_integrable x)) x0 x1,
      RiemannInt outer_integrable = value.

Theorem area_disc :
  forall (center : (R * R)%type) (radius : R),
    0 <= radius ->
    iterated_Riemann_integral
      (fun x y => disc_indicator center radius (x, y))
      (fst center - radius) (fst center + radius)
      (snd center - radius) (snd center + radius)
      (PI * radius ^ 2).
Admitted.
