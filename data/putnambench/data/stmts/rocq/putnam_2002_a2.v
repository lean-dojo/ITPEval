(* Statement-only formalization of PutnamBench corpus artifact putnam_2002_a2:
   among any five points on the unit sphere in real three-space, some four
   lie in a common closed hemisphere. This file contains no proof. *)

From Stdlib Require Import Reals Lists.List.

Open Scope R_scope.

Record putnam_2002_a2_vec3 : Type := {
  putnam_2002_a2_x : R;
  putnam_2002_a2_y : R;
  putnam_2002_a2_z : R
}.

Definition putnam_2002_a2_point_set : Type :=
  putnam_2002_a2_vec3 -> Prop.

Definition putnam_2002_a2_zero : putnam_2002_a2_vec3 :=
  {| putnam_2002_a2_x := 0;
     putnam_2002_a2_y := 0;
     putnam_2002_a2_z := 0 |}.

Definition putnam_2002_a2_dot
    (u v : putnam_2002_a2_vec3) : R :=
  putnam_2002_a2_x u * putnam_2002_a2_x v +
  putnam_2002_a2_y u * putnam_2002_a2_y v +
  putnam_2002_a2_z u * putnam_2002_a2_z v.

Definition putnam_2002_a2_unit_sphere : putnam_2002_a2_point_set :=
  fun p : putnam_2002_a2_vec3 =>
    putnam_2002_a2_dot p p = 1.

Definition putnam_2002_a2_hemisphere
    (normal : putnam_2002_a2_vec3) : putnam_2002_a2_point_set :=
  fun p : putnam_2002_a2_vec3 =>
    0 <= putnam_2002_a2_dot p normal.

Definition putnam_2002_a2_subset
    (A B : putnam_2002_a2_point_set) : Prop :=
  forall p : putnam_2002_a2_vec3, A p -> B p.

Definition putnam_2002_a2_intersection
    (A B : putnam_2002_a2_point_set) : putnam_2002_a2_point_set :=
  fun p : putnam_2002_a2_vec3 => A p /\ B p.

Definition putnam_2002_a2_has_cardinality
    (A : putnam_2002_a2_point_set) (n : nat) : Prop :=
  exists enumeration : list putnam_2002_a2_vec3,
    NoDup enumeration /\
    length enumeration = n /\
    forall p : putnam_2002_a2_vec3,
      List.In p enumeration <-> A p.

Theorem putnam_2002_a2 :
  forall S : putnam_2002_a2_point_set,
    putnam_2002_a2_subset S putnam_2002_a2_unit_sphere /\
    putnam_2002_a2_has_cardinality S 5%nat ->
    exists normal : putnam_2002_a2_vec3,
      normal <> putnam_2002_a2_zero /\
      exists k : nat,
        putnam_2002_a2_has_cardinality
          (putnam_2002_a2_intersection
            S (putnam_2002_a2_hemisphere normal))
          k /\
        (4 <= k)%nat.
Admitted.
