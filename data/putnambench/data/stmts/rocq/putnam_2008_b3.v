(* Statement-only formalization of PutnamBench corpus artifact putnam_2008_b3:
   the largest radius of a circle contained in a four-dimensional hypercube
   of side length one. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Record putnam_2008_b3_point4 := {
  putnam_2008_b3_x0 : R;
  putnam_2008_b3_x1 : R;
  putnam_2008_b3_x2 : R;
  putnam_2008_b3_x3 : R
}.

Definition putnam_2008_b3_zero : putnam_2008_b3_point4 :=
  {| putnam_2008_b3_x0 := 0;
     putnam_2008_b3_x1 := 0;
     putnam_2008_b3_x2 := 0;
     putnam_2008_b3_x3 := 0 |}.

Definition putnam_2008_b3_add
    (p q : putnam_2008_b3_point4) : putnam_2008_b3_point4 :=
  {| putnam_2008_b3_x0 := putnam_2008_b3_x0 p + putnam_2008_b3_x0 q;
     putnam_2008_b3_x1 := putnam_2008_b3_x1 p + putnam_2008_b3_x1 q;
     putnam_2008_b3_x2 := putnam_2008_b3_x2 p + putnam_2008_b3_x2 q;
     putnam_2008_b3_x3 := putnam_2008_b3_x3 p + putnam_2008_b3_x3 q |}.

Definition putnam_2008_b3_scale
    (a : R) (p : putnam_2008_b3_point4) : putnam_2008_b3_point4 :=
  {| putnam_2008_b3_x0 := a * putnam_2008_b3_x0 p;
     putnam_2008_b3_x1 := a * putnam_2008_b3_x1 p;
     putnam_2008_b3_x2 := a * putnam_2008_b3_x2 p;
     putnam_2008_b3_x3 := a * putnam_2008_b3_x3 p |}.

Definition putnam_2008_b3_norm
    (p : putnam_2008_b3_point4) : R :=
  sqrt
    (putnam_2008_b3_x0 p ^ 2 +
     putnam_2008_b3_x1 p ^ 2 +
     putnam_2008_b3_x2 p ^ 2 +
     putnam_2008_b3_x3 p ^ 2).

Definition putnam_2008_b3_in_hypercube
    (p : putnam_2008_b3_point4) : Prop :=
  Rabs (putnam_2008_b3_x0 p) <= 1 / 2 /\
  Rabs (putnam_2008_b3_x1 p) <= 1 / 2 /\
  Rabs (putnam_2008_b3_x2 p) <= 1 / 2 /\
  Rabs (putnam_2008_b3_x3 p) <= 1 / 2.

Definition putnam_2008_b3_linearly_independent
    (u v : putnam_2008_b3_point4) : Prop :=
  forall a b : R,
    putnam_2008_b3_add
      (putnam_2008_b3_scale a u)
      (putnam_2008_b3_scale b v) =
    putnam_2008_b3_zero ->
    a = 0 /\ b = 0.

Definition putnam_2008_b3_offset
    (u v : putnam_2008_b3_point4) (s t : R) :
    putnam_2008_b3_point4 :=
  putnam_2008_b3_add
    (putnam_2008_b3_scale s u)
    (putnam_2008_b3_scale t v).

Definition putnam_2008_b3_contains_circle (r : R) : Prop :=
  exists center u v : putnam_2008_b3_point4,
    putnam_2008_b3_linearly_independent u v /\
    forall s t : R,
      putnam_2008_b3_norm (putnam_2008_b3_offset u v s t) = r ->
      putnam_2008_b3_in_hypercube
        (putnam_2008_b3_add center
          (putnam_2008_b3_offset u v s t)).

Definition putnam_2008_b3_solution : R := sqrt 2 / 2.

Theorem putnam_2008_b3 :
  putnam_2008_b3_contains_circle putnam_2008_b3_solution /\
  forall r : R,
    putnam_2008_b3_solution < r ->
    ~ putnam_2008_b3_contains_circle r.
Admitted.
