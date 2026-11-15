(*
  Statement-only formalization of "The Isoperimetric Theorem" from Hundred Theorems item 043.
  It states the sharp area bound for rectifiable simple closed plane curves and characterizes
  equality by a circular image. This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalEpsilon.

Local Open Scope R_scope.

Definition point := (R * R)%type.
Definition region := point -> Prop.
Definition plane_path := R -> point.

Definition unit_interval (t : R) : Prop :=
  0 <= t <= 1.

Definition path_image (gamma : plane_path) : region :=
  fun z => exists t : R, unit_interval t /\ gamma t = z.

Definition path_start (gamma : plane_path) : point :=
  gamma 0.

Definition path_finish (gamma : plane_path) : point :=
  gamma 1.

Definition point_distance (p q : point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition sphere (center : point) (radius : R) : region :=
  fun p => point_distance p center = radius.

Definition same_region (s t : region) : Prop :=
  forall p : point, s p <-> t p.

Definition continuous_on_unit (gamma : plane_path) : Prop :=
  forall t : R, unit_interval t ->
  forall epsilon : R, 0 < epsilon ->
  exists delta : R, 0 < delta /\
    forall u : R, unit_interval u ->
      Rabs (u - t) < delta ->
      point_distance (gamma u) (gamma t) < epsilon.

Definition simple_path (gamma : plane_path) : Prop :=
  continuous_on_unit gamma /\
  forall s t : R, unit_interval s -> unit_interval t ->
    gamma s = gamma t ->
    s = t \/ (s = 0 /\ t = 1) \/ (s = 1 /\ t = 0).

Definition unit_partition (partition : nat -> R) (n : nat) : Prop :=
  partition O = 0 /\
  partition n = 1 /\
  forall i : nat, (i < n)%nat ->
    partition i <= partition (S i).

Fixpoint polygonal_length
    (gamma : plane_path) (partition : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      polygonal_length gamma partition k +
      point_distance (gamma (partition k)) (gamma (partition (S k)))
  end.

Definition variation_upper_bound (gamma : plane_path) (bound : R) : Prop :=
  forall (n : nat) (partition : nat -> R),
    unit_partition partition n ->
    polygonal_length gamma partition n <= bound.

Definition rectifiable_path (gamma : plane_path) : Prop :=
  continuous_on_unit gamma /\
  exists bound : R, variation_upper_bound gamma bound.

Definition is_path_length (gamma : plane_path) (length : R) : Prop :=
  variation_upper_bound gamma length /\
  forall bound : R, variation_upper_bound gamma bound -> length <= bound.

Definition path_length (gamma : plane_path) : R :=
  epsilon (inhabits 0%R) (is_path_length gamma).

Definition open_region (s : region) : Prop :=
  forall p : point, s p ->
  exists epsilon : R, 0 < epsilon /\
    forall q : point, point_distance q p < epsilon -> s q.

Definition relatively_open (carrier subset : region) : Prop :=
  exists ambient : region, open_region ambient /\
    forall p : point, subset p <-> carrier p /\ ambient p.

Definition connected_region (carrier : region) : Prop :=
  forall left right : region,
    relatively_open carrier left ->
    relatively_open carrier right ->
    (forall p : point, carrier p <-> left p \/ right p) ->
    (forall p : point, ~ (left p /\ right p)) ->
    (forall p : point, ~ left p) \/ (forall p : point, ~ right p).

Definition complement_component
    (boundary : region) (base : point) : region :=
  fun p =>
    exists carrier : region,
      connected_region carrier /\
      carrier base /\
      carrier p /\
      forall q : point, carrier q -> ~ boundary q.

Definition bounded_region (s : region) : Prop :=
  exists bound : R, forall p : point, s p ->
    point_distance p (0, 0) <= bound.

Definition inside (boundary : region) : region :=
  fun p =>
    ~ boundary p /\
    bounded_region (complement_component boundary p).

Record open_rectangle := {
  x_lower : R;
  x_upper : R;
  y_lower : R;
  y_upper : R
}.

Definition in_open_rectangle
    (rectangle : open_rectangle) (p : point) : Prop :=
  x_lower rectangle < fst p < x_upper rectangle /\
  y_lower rectangle < snd p < y_upper rectangle.

Definition rectangle_area (rectangle : open_rectangle) : R :=
  Rmax 0 (x_upper rectangle - x_lower rectangle) *
  Rmax 0 (y_upper rectangle - y_lower rectangle).

Definition rectangles_cover
    (s : region) (rectangles : nat -> open_rectangle) : Prop :=
  forall p : point, s p ->
    exists n : nat, in_open_rectangle (rectangles n) p.

Fixpoint partial_area
    (rectangles : nat -> open_rectangle) (n : nat) : R :=
  match n with
  | O => 0
  | S k => partial_area rectangles k + rectangle_area (rectangles k)
  end.

Definition converges_to (sequence : nat -> R) (limit : R) : Prop :=
  forall epsilon : R, 0 < epsilon ->
  exists N : nat, forall n : nat, (N <= n)%nat ->
    Rabs (sequence n - limit) < epsilon.

Definition cover_cost (s : region) (cost : R) : Prop :=
  exists rectangles : nat -> open_rectangle,
    rectangles_cover s rectangles /\
    converges_to (partial_area rectangles) cost.

(* The infimum of countable open-rectangle cover costs is planar outer area. *)
Definition is_outer_area (s : region) (area : R) : Prop :=
  (forall cost : R, cover_cost s cost -> area <= cost) /\
  (forall lower_bound : R,
      (forall cost : R, cover_cost s cost -> lower_bound <= cost) ->
      lower_bound <= area).

Definition area_measure (s : region) : R :=
  epsilon (inhabits 0%R) (is_outer_area s).

Theorem isoperimetric_theorem :
  forall (L : R) (gamma : plane_path),
    rectifiable_path gamma ->
    simple_path gamma ->
    path_finish gamma = path_start gamma ->
    path_length gamma = L ->
    area_measure (inside (path_image gamma)) <= L ^ 2 / (4 * PI) /\
    (area_measure (inside (path_image gamma)) = L ^ 2 / (4 * PI) ->
     exists (center : point) (radius : R),
       same_region (path_image gamma) (sphere center radius)).
Admitted.
