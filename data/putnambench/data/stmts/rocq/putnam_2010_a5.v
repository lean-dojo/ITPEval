(* Statement-only formalization of PutnamBench corpus artifact putnam_2010_a5:
   a group embedded in real three-space whose products agree with cross
   products unless those cross products vanish. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2010_a5_vector : Type := (R * (R * R))%type.

Definition putnam_2010_a5_cross
    (u v : putnam_2010_a5_vector) : putnam_2010_a5_vector :=
  let '(ux, (uy, uz)) := u in
  let '(vx, (vy, vz)) := v in
  (uy * vz - uz * vy,
   (uz * vx - ux * vz,
    ux * vy - uy * vx)).

Definition putnam_2010_a5_zero : putnam_2010_a5_vector :=
  (0, (0, 0)).

Record putnam_2010_a5_group (G : Type) : Type := {
  putnam_2010_a5_mul : G -> G -> G;
  putnam_2010_a5_one : G;
  putnam_2010_a5_inv : G -> G;
  putnam_2010_a5_assoc :
    forall x y z : G,
      putnam_2010_a5_mul x (putnam_2010_a5_mul y z) =
      putnam_2010_a5_mul (putnam_2010_a5_mul x y) z;
  putnam_2010_a5_left_identity :
    forall x : G, putnam_2010_a5_mul putnam_2010_a5_one x = x;
  putnam_2010_a5_right_identity :
    forall x : G, putnam_2010_a5_mul x putnam_2010_a5_one = x;
  putnam_2010_a5_left_inverse :
    forall x : G,
      putnam_2010_a5_mul (putnam_2010_a5_inv x) x =
      putnam_2010_a5_one;
  putnam_2010_a5_right_inverse :
    forall x : G,
      putnam_2010_a5_mul x (putnam_2010_a5_inv x) =
      putnam_2010_a5_one
}.

Arguments putnam_2010_a5_mul {G} _ _ _.

Theorem putnam_2010_a5
    (G : Type)
    (grp : putnam_2010_a5_group G)
    (i : G -> putnam_2010_a5_vector)
    (i_injective :
      forall x y : G, i x = i y -> x = y)
    (hcross :
      forall a b : G,
        putnam_2010_a5_cross (i a) (i b) =
          i (putnam_2010_a5_mul grp a b) \/
        putnam_2010_a5_cross (i a) (i b) =
          putnam_2010_a5_zero) :
  forall a b : G,
    putnam_2010_a5_cross (i a) (i b) =
      putnam_2010_a5_zero.
Admitted.
