(*
  Statement-only formalization of "Green's Theorem" from Hundred Theorems
  artifact 021: the positively oriented line integral of a C1 plane field
  equals the area integral of its scalar curl. This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription.

#[local] Open Scope R_scope.

Definition point := (R * R)%type.
Definition region := point -> Prop.
Definition scalar_field := point -> R.
Definition plane_path := R -> point.

Definition point_x (z : point) : R := fst z.
Definition point_y (z : point) : R := snd z.

Definition point_distance (z w : point) : R :=
  sqrt ((point_x z - point_x w) ^ 2 + (point_y z - point_y w) ^ 2).

Definition point_norm (z : point) : R := point_distance z (0, 0).

Definition unit_interval (t : R) : Prop := 0 <= t <= 1.

Definition path_image (gamma : plane_path) : region :=
  fun z => exists t : R, unit_interval t /\ gamma t = z.

Definition region_union (s t : region) : region :=
  fun z => s z \/ t z.

Definition included (s t : region) : Prop :=
  forall z : point, s z -> t z.

Definition open_region (u : region) : Prop :=
  forall z : point, u z ->
    exists delta : R, 0 < delta /\
      forall w : point, point_distance w z < delta -> u w.

Definition scalar_continuous_on (f : scalar_field) (u : region) : Prop :=
  forall z : point, u z ->
    forall epsilon : R, 0 < epsilon ->
      exists delta : R, 0 < delta /\
        forall w : point, u w ->
          point_distance w z < delta ->
          Rabs (f w - f z) < epsilon.

Definition plane_continuous_on
    (gamma : plane_path) (domain : R -> Prop) : Prop :=
  forall t : R, domain t ->
    forall epsilon : R, 0 < epsilon ->
      exists delta : R, 0 < delta /\
        forall s : R, domain s ->
          Rabs (s - t) < delta ->
          point_distance (gamma s) (gamma t) < epsilon.

Definition is_partial_derivative_x
    (f derivative : scalar_field) (u : region) : Prop :=
  forall z : point, u z ->
    forall epsilon : R, 0 < epsilon ->
      exists delta : R, 0 < delta /\
        forall h : R, 0 < Rabs h < delta ->
          Rabs
            ((f (point_x z + h, point_y z) - f z) / h - derivative z)
          < epsilon.

Definition is_partial_derivative_y
    (f derivative : scalar_field) (u : region) : Prop :=
  forall z : point, u z ->
    forall epsilon : R, 0 < epsilon ->
      exists delta : R, 0 < delta /\
        forall h : R, 0 < Rabs h < delta ->
          Rabs
            ((f (point_x z, point_y z + h) - f z) / h - derivative z)
          < epsilon.

Definition continuously_differentiable_on
    (f : scalar_field) (u : region) : Prop :=
  exists d_dx d_dy : scalar_field,
    is_partial_derivative_x f d_dx u /\
    is_partial_derivative_y f d_dy u /\
    scalar_continuous_on d_dx u /\
    scalar_continuous_on d_dy u.

Fixpoint sum_n (n : nat) (f : nat -> R) : R :=
  match n with
  | O => 0
  | S k => sum_n k f + f k
  end.

Definition ordered_interval_family
    (n : nat) (a b : nat -> R) : Prop :=
  (forall i : nat, (i < n)%nat ->
    unit_interval (a i) /\
    unit_interval (b i) /\
    a i <= b i) /\
  (forall i : nat, (S i < n)%nat -> b i <= a (S i)).

Definition absolutely_continuous_on_unit_interval
    (gamma : plane_path) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists delta : R, 0 < delta /\
      forall (n : nat) (a b : nat -> R),
        ordered_interval_family n a b ->
        sum_n n (fun i => b i - a i) < delta ->
        sum_n n (fun i => point_distance (gamma (b i)) (gamma (a i)))
          < epsilon.

Definition path_connected_avoiding
    (s : region) (z w : point) : Prop :=
  exists c : plane_path,
    c 0 = z /\
    c 1 = w /\
    plane_continuous_on c unit_interval /\
    forall t : R, unit_interval t -> ~ s (c t).

Definition inside (s : region) : region :=
  fun z =>
    ~ s z /\
    exists bound : R, 0 <= bound /\
      forall w : point,
        ~ s w ->
        path_connected_avoiding s z w ->
        point_norm w <= bound.

Definition tagged_partition
    (n : nat) (partition tags : nat -> R) : Prop :=
  (0 < n)%nat /\
  partition 0%nat = 0 /\
  partition n = 1 /\
  forall i : nat, (i < n)%nat ->
    partition i < partition (S i) /\
    partition i <= tags i <= partition (S i).

Definition line_sum
    (P Q : scalar_field) (gamma : plane_path)
    (n : nat) (partition tags : nat -> R) : R :=
  sum_n n
    (fun i =>
      P (gamma (tags i)) *
        (point_x (gamma (partition (S i))) -
         point_x (gamma (partition i))) +
      Q (gamma (tags i)) *
        (point_y (gamma (partition (S i))) -
         point_y (gamma (partition i)))).

Definition line_integral_has_value
    (P Q : scalar_field) (gamma : plane_path) (value : R) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists delta : R, 0 < delta /\
      forall (n : nat) (partition tags : nat -> R),
        tagged_partition n partition tags ->
        (forall i : nat, (i < n)%nat ->
          partition (S i) - partition i < delta) ->
        Rabs (line_sum P Q gamma n partition tags - value) < epsilon.

Definition winding_P (z : point) : scalar_field :=
  fun w =>
    - (point_y w - point_y z) /
      ((point_x w - point_x z) ^ 2 + (point_y w - point_y z) ^ 2).

Definition winding_Q (z : point) : scalar_field :=
  fun w =>
    (point_x w - point_x z) /
      ((point_x w - point_x z) ^ 2 + (point_y w - point_y z) ^ 2).

Definition has_positive_winding (gamma : plane_path) : Prop :=
  forall z : point,
    inside (path_image gamma) z ->
    line_integral_has_value (winding_P z) (winding_Q z) gamma (2 * PI).

Definition closed_square (bound : R) : region :=
  fun z =>
    - bound <= point_x z <= bound /\
    - bound <= point_y z <= bound.

Definition grid_width (bound : R) (n : nat) : R :=
  (2 * bound) / INR n.

Definition square_grid_tags
    (bound : R) (n : nat) (tags : nat -> nat -> point) : Prop :=
  forall i j : nat, (i < n)%nat -> (j < n)%nat ->
    - bound + INR i * grid_width bound n <= point_x (tags i j) <=
      - bound + INR (S i) * grid_width bound n /\
    - bound + INR j * grid_width bound n <= point_y (tags i j) <=
      - bound + INR (S j) * grid_width bound n.

Definition region_sample
    (f : scalar_field) (s : region) (z : point) : R :=
  if excluded_middle_informative (s z) then f z else 0.

Definition square_grid_sum
    (f : scalar_field) (s : region) (bound : R)
    (n : nat) (tags : nat -> nat -> point) : R :=
  (grid_width bound n) ^ 2 *
  sum_n n
    (fun i => sum_n n (fun j => region_sample f s (tags i j))).

Definition area_integral_has_value
    (f : scalar_field) (s : region) (value : R) : Prop :=
  exists bound : R, 0 < bound /\
    included s (closed_square bound) /\
    forall epsilon : R, 0 < epsilon ->
      exists N : nat,
        forall (n : nat) (tags : nat -> nat -> point),
          (N <= n)%nat ->
          (0 < n)%nat ->
          square_grid_tags bound n tags ->
          Rabs (square_grid_sum f s bound n tags - value) < epsilon.

Definition curl (dQ_dx dP_dy : scalar_field) : scalar_field :=
  fun z => dQ_dx z - dP_dy z.

Theorem green_s_theorem :
  forall (P Q dQ_dx dP_dy : scalar_field)
         (gamma : plane_path) (u : region),
    absolutely_continuous_on_unit_interval gamma ->
    gamma 1 = gamma 0 ->
    has_positive_winding gamma ->
    open_region u ->
    included
      (region_union (inside (path_image gamma)) (path_image gamma))
      u ->
    continuously_differentiable_on P u ->
    continuously_differentiable_on Q u ->
    is_partial_derivative_x Q dQ_dx u ->
    is_partial_derivative_y P dP_dy u ->
    exists area_value line_value : R,
      area_integral_has_value
        (curl dQ_dx dP_dy)
        (inside (path_image gamma))
        area_value /\
      line_integral_has_value P Q gamma line_value /\
      line_value = area_value.
Admitted.
