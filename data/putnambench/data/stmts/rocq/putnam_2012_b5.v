(* Statement-only formalization of PutnamBench corpus artifact putnam_2012_b5:
   the supremum of a power-product family from two bounded real functions
   represented as a maximum of affine functions. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2012_b5_is_supremum
    (values : R -> Prop) (bound : R) : Prop :=
  (forall value : R, values value -> value <= bound) /\
  (forall upper : R,
      (forall value : R, values value -> value <= upper) ->
      bound <= upper).

Definition putnam_2012_b5_power_values
    (g1 g2 : R -> R) (x : R) : R -> Prop :=
  fun value : R =>
    exists s : R, value = Rpower (g1 s) x * g2 s.

Definition putnam_2012_b5_affine_values
    (h1 h2 : R -> R) (x : R) : R -> Prop :=
  fun value : R =>
    exists t : R, value = x * h1 t + h2 t.

Definition putnam_2012_b5_is_maximum
    (values : R -> Prop) (maximum : R) : Prop :=
  values maximum /\
  forall value : R, values value -> value <= maximum.

Theorem putnam_2012_b5
    (g1 g2 : R -> R)
    (hgim : forall x : R, 1 <= g1 x /\ 1 <= g2 x)
    (hgbd :
      exists B1 B2 : R,
        forall x : R, g1 x <= B1 /\ g2 x <= B2) :
  exists h1 h2 : R -> R,
    forall x : R,
      exists bound : R,
        putnam_2012_b5_is_supremum
          (putnam_2012_b5_power_values g1 g2 x) bound /\
        putnam_2012_b5_is_maximum
          (putnam_2012_b5_affine_values h1 h2 x) bound.
Admitted.
