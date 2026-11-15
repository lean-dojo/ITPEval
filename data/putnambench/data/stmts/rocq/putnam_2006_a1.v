(* Statement-only formalization of PutnamBench corpus artifact putnam_2006_a1:
   the three-dimensional Lebesgue volume of the real region satisfying
   (x^2 + y^2 + z^2 + 8)^2 <= 36(x^2 + y^2) is 6*pi^2.
   This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2006_a1_point : Type := (R * (R * R))%type.
Definition putnam_2006_a1_point_set : Type :=
  putnam_2006_a1_point -> Prop.

Definition putnam_2006_a1_x (p : putnam_2006_a1_point) : R :=
  fst p.

Definition putnam_2006_a1_y (p : putnam_2006_a1_point) : R :=
  fst (snd p).

Definition putnam_2006_a1_z (p : putnam_2006_a1_point) : R :=
  snd (snd p).

Definition putnam_2006_a1_region : putnam_2006_a1_point_set :=
  fun p : putnam_2006_a1_point =>
    (putnam_2006_a1_x p ^ 2 +
     putnam_2006_a1_y p ^ 2 +
     putnam_2006_a1_z p ^ 2 + 8) ^ 2 <=
    36 *
    (putnam_2006_a1_x p ^ 2 +
     putnam_2006_a1_y p ^ 2).

Record putnam_2006_a1_open_box : Type := {
  putnam_2006_a1_x_lower : R;
  putnam_2006_a1_x_upper : R;
  putnam_2006_a1_y_lower : R;
  putnam_2006_a1_y_upper : R;
  putnam_2006_a1_z_lower : R;
  putnam_2006_a1_z_upper : R
}.

Definition putnam_2006_a1_in_open_box
    (box : putnam_2006_a1_open_box)
    (p : putnam_2006_a1_point) : Prop :=
  putnam_2006_a1_x_lower box < putnam_2006_a1_x p <
    putnam_2006_a1_x_upper box /\
  putnam_2006_a1_y_lower box < putnam_2006_a1_y p <
    putnam_2006_a1_y_upper box /\
  putnam_2006_a1_z_lower box < putnam_2006_a1_z p <
    putnam_2006_a1_z_upper box.

Definition putnam_2006_a1_box_volume
    (box : putnam_2006_a1_open_box) : R :=
  Rmax 0
    (putnam_2006_a1_x_upper box -
     putnam_2006_a1_x_lower box) *
  Rmax 0
    (putnam_2006_a1_y_upper box -
     putnam_2006_a1_y_lower box) *
  Rmax 0
    (putnam_2006_a1_z_upper box -
     putnam_2006_a1_z_lower box).

Definition putnam_2006_a1_boxes_cover
    (A : putnam_2006_a1_point_set)
    (boxes : nat -> putnam_2006_a1_open_box) : Prop :=
  forall p : putnam_2006_a1_point,
    A p ->
    exists n : nat, putnam_2006_a1_in_open_box (boxes n) p.

Fixpoint putnam_2006_a1_partial_box_volume
    (boxes : nat -> putnam_2006_a1_open_box)
    (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      putnam_2006_a1_partial_box_volume boxes k +
      putnam_2006_a1_box_volume (boxes k)
  end.

(* Equality with finite three-dimensional Lebesgue outer measure, expressed
   through countable open-box covers. On the closed region above, this is its
   three-dimensional Lebesgue measure. *)
Definition putnam_2006_a1_has_spatial_lebesgue_measure
    (A : putnam_2006_a1_point_set) (volume : R) : Prop :=
  0 <= volume /\
  (forall boxes : nat -> putnam_2006_a1_open_box,
    putnam_2006_a1_boxes_cover A boxes ->
    forall lower : R,
      lower < volume ->
      exists n : nat,
        lower < putnam_2006_a1_partial_box_volume boxes n) /\
  (forall epsilon : R,
    0 < epsilon ->
    exists boxes : nat -> putnam_2006_a1_open_box,
      putnam_2006_a1_boxes_cover A boxes /\
      forall n : nat,
        putnam_2006_a1_partial_box_volume boxes n <
        volume + epsilon).

Definition putnam_2006_a1_solution : R := 6 * PI ^ 2.

Theorem putnam_2006_a1 :
  putnam_2006_a1_has_spatial_lebesgue_measure
    putnam_2006_a1_region
    putnam_2006_a1_solution.
Admitted.
