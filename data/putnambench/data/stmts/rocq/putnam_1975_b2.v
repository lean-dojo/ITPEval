(* Statement-only formalization of PutnamBench artifact putnam_1975_b2:
   a sequence of open slabs in three-dimensional Euclidean space whose
   positive thicknesses have convergent partial sums cannot cover the whole
   space. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Record putnam_1975_b2_vec3 := {
  putnam_1975_b2_x : R;
  putnam_1975_b2_y : R;
  putnam_1975_b2_z : R
}.

Definition putnam_1975_b2_dot
    (u v : putnam_1975_b2_vec3) : R :=
  putnam_1975_b2_x u * putnam_1975_b2_x v +
  putnam_1975_b2_y u * putnam_1975_b2_y v +
  putnam_1975_b2_z u * putnam_1975_b2_z v.

Definition putnam_1975_b2_norm
    (u : putnam_1975_b2_vec3) : R :=
  sqrt (putnam_1975_b2_dot u u).

Definition putnam_1975_b2_slab
    (normal : putnam_1975_b2_vec3)
    (offset thickness : R)
    (p : putnam_1975_b2_vec3) : Prop :=
  offset < putnam_1975_b2_dot normal p <
    offset + thickness.

Fixpoint putnam_1975_b2_partial_sum
    (f : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => putnam_1975_b2_partial_sum f k + f k
  end.

Definition putnam_1975_b2_partial_sums_converge
    (f : nat -> R) : Prop :=
  exists limit : R,
    forall epsilon : R,
      0 < epsilon ->
      exists N : nat,
        forall n : nat,
          (N <= n)%nat ->
          Rabs (putnam_1975_b2_partial_sum f n - limit) < epsilon.

Theorem putnam_1975_b2
    (normals : nat -> putnam_1975_b2_vec3)
    (offsets thicknesses : nat -> R)
    (hnormalsunit :
      forall i : nat, putnam_1975_b2_norm (normals i) = 1)
    (hthicknessespos :
      forall i : nat, 0 < thicknesses i)
    (hthicknessesconv :
      putnam_1975_b2_partial_sums_converge thicknesses) :
  exists p : putnam_1975_b2_vec3,
    forall i : nat,
      ~ putnam_1975_b2_slab
          (normals i) (offsets i) (thicknesses i) p.
Admitted.
