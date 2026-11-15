(*
  Statement-only formalization of "Dissection of Cubes (into Cubes)" from
  Hundred Theorems artifact 082. It states that no finite, nontrivial,
  pairwise-disjoint dissection of the three-dimensional real unit cube into
  axis-aligned cubes can have pairwise distinct positive widths.
  This file contains no proof.
*)

From Stdlib Require Import Reals List.

Local Open Scope R_scope.

Record point3 : Type := {
  point_x : R;
  point_y : R;
  point_z : R
}.

Record cube3 : Type := {
  cube_lower : point3;
  cube_width : R
}.

Definition in_half_open_cube (cube : cube3) (point : point3) : Prop :=
  point_x (cube_lower cube) <= point_x point <
    point_x (cube_lower cube) + cube_width cube /\
  point_y (cube_lower cube) <= point_y point <
    point_y (cube_lower cube) + cube_width cube /\
  point_z (cube_lower cube) <= point_z point <
    point_z (cube_lower cube) + cube_width cube.

Definition unit_cube : cube3 :=
  {| cube_lower :=
       {| point_x := 0;
          point_y := 0;
          point_z := 0 |};
     cube_width := 1 |}.

Definition finite_cube_family (family : cube3 -> Prop) : Prop :=
  exists enumeration : list cube3,
    NoDup enumeration /\
    forall cube : cube3, family cube <-> In cube enumeration.

Definition nontrivial_cube_family (family : cube3 -> Prop) : Prop :=
  exists first second : cube3,
    family first /\
    family second /\
    first <> second.

Definition positive_cube_widths (family : cube3 -> Prop) : Prop :=
  forall cube : cube3,
    family cube ->
    0 < cube_width cube.

Definition pairwise_disjoint_cubes (family : cube3 -> Prop) : Prop :=
  forall first second : cube3,
    family first ->
    family second ->
    first <> second ->
    forall point : point3,
      ~ (in_half_open_cube first point /\
         in_half_open_cube second point).

Definition covers_unit_cube (family : cube3 -> Prop) : Prop :=
  forall point : point3,
    in_half_open_cube unit_cube point <->
    exists cube : cube3,
      family cube /\ in_half_open_cube cube point.

Definition pairwise_distinct_widths (family : cube3 -> Prop) : Prop :=
  forall first second : cube3,
    family first ->
    family second ->
    cube_width first = cube_width second ->
    first = second.

Theorem dissection_of_cubes_into_cubes :
  ~ exists family : cube3 -> Prop,
      finite_cube_family family /\
      nontrivial_cube_family family /\
      positive_cube_widths family /\
      pairwise_disjoint_cubes family /\
      covers_unit_cube family /\
      pairwise_distinct_widths family.
Admitted.
