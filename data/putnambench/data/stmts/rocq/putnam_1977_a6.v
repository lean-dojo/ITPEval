(* Statement-only formalization of PutnamBench artifact putnam_1977_a6: vanishing integrals over maximal centered squares for a continuous real function imply pointwise vanishing on the unit square; this file contains no proof. *)
From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_1977_a6_solution : Prop := True.

Definition putnam_1977_a6_unit_square (p : (R * R)%type) : Prop :=
  0 <= fst p <= 1 /\ 0 <= snd p <= 1.

Definition putnam_1977_a6_room (p : (R * R)%type) : R :=
  Rmin (Rmin (fst p) (1 - fst p))
       (Rmin (snd p) (1 - snd p)).

Definition putnam_1977_a6_continuous
    (f : (R * R)%type -> R) : Prop :=
  forall x y eps : R,
    eps > 0 ->
    exists delta : R,
      delta > 0 /\
      forall x' y' : R,
        Rabs (x' - x) < delta ->
        Rabs (y' - y) < delta ->
        Rabs (f (x', y') - f (x, y)) < eps.

Definition putnam_1977_a6_square_integral_has_value
    (f : (R * R)%type -> R) (p : (R * R)%type)
    (value : R) : Prop :=
  exists inner_integral : R -> R,
    (forall x : R,
      exists inner_integrable :
        Riemann_integrable
          (fun y : R => f (x, y))
          (snd p - putnam_1977_a6_room p)
          (snd p + putnam_1977_a6_room p),
        inner_integral x = RiemannInt inner_integrable) /\
    exists outer_integrable :
      Riemann_integrable
        inner_integral
        (fst p - putnam_1977_a6_room p)
        (fst p + putnam_1977_a6_room p),
      value = RiemannInt outer_integrable.

Theorem putnam_1977_a6 :
  ((forall f : (R * R)%type -> R,
      putnam_1977_a6_continuous f ->
      (forall p : (R * R)%type,
        putnam_1977_a6_unit_square p ->
        putnam_1977_a6_square_integral_has_value f p 0) ->
      forall p : (R * R)%type,
        putnam_1977_a6_unit_square p ->
        f p = 0) <->
    putnam_1977_a6_solution).
Admitted.
