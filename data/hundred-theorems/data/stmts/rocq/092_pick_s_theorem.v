(*
  Statement-only formalization of Hundred Theorems artifact 092,
  "Pick's Theorem": the area of a simple lattice polygon is its number
  of interior lattice points plus half its boundary lattice points minus one.
  This file contains no proof.
*)

From Stdlib Require Import Reals List ZArith PeanoNat.

Import ListNotations.
Open Scope R_scope.

Definition point := (R * R)%type.
Definition edge := (point * point)%type.

Definition point_x (p : point) : R := fst p.
Definition point_y (p : point) : R := snd p.

Fixpoint edges_from
    (first current : point) (remaining : list point) : list edge :=
  match remaining with
  | [] => [(current, first)]
  | next :: rest =>
      (current, next) :: edges_from first next rest
  end.

Definition polygon_edges (vertices : list point) : list edge :=
  match vertices with
  | [] => []
  | first :: rest => edges_from first first rest
  end.

Definition orientation (a b p : point) : R :=
  (point_x b - point_x a) * (point_y p - point_y a) -
  (point_y b - point_y a) * (point_x p - point_x a).

Definition point_on_segment (p : point) (e : edge) : Prop :=
  let a := fst e in
  let b := snd e in
  orientation a b p = 0 /\
  Rmin (point_x a) (point_x b) <= point_x p <=
    Rmax (point_x a) (point_x b) /\
  Rmin (point_y a) (point_y b) <= point_y p <=
    Rmax (point_y a) (point_y b).

Definition common_endpoint (p : point) (e1 e2 : edge) : Prop :=
  (p = fst e1 \/ p = snd e1) /\
  (p = fst e2 \/ p = snd e2).

Definition simple_polygon (vertices : list point) : Prop :=
  (3 <= length vertices)%nat /\
  NoDup vertices /\
  (forall e : edge,
      In e (polygon_edges vertices) ->
      fst e <> snd e) /\
  (forall (e1 e2 : edge),
      In e1 (polygon_edges vertices) ->
      In e2 (polygon_edges vertices) ->
      e1 <> e2 ->
      forall p : point,
        point_on_segment p e1 ->
        point_on_segment p e2 ->
        common_endpoint p e1 e2).

Definition integral_point (p : point) : Prop :=
  exists m n : Z,
    point_x p = IZR m /\ point_y p = IZR n.

Definition on_polygon_boundary
    (vertices : list point) (p : point) : Prop :=
  exists e : edge,
    In e (polygon_edges vertices) /\ point_on_segment p e.

Definition crossing_index (p : point) (e : edge) : Z :=
  let a := fst e in
  let b := snd e in
  if Rle_dec (point_y a) (point_y p) then
    if Rlt_dec (point_y p) (point_y b) then
      if Rlt_dec 0 (orientation a b p) then 1%Z else 0%Z
    else 0%Z
  else if Rle_dec (point_y b) (point_y p) then
    if Rlt_dec (point_y p) (point_y a) then
      if Rlt_dec (orientation a b p) 0 then (-1)%Z else 0%Z
    else 0%Z
  else 0%Z.

Fixpoint winding_number_edges
    (p : point) (es : list edge) : Z :=
  match es with
  | [] => 0%Z
  | e :: rest =>
      (crossing_index p e + winding_number_edges p rest)%Z
  end.

Definition winding_number (vertices : list point) (p : point) : Z :=
  winding_number_edges p (polygon_edges vertices).

Definition in_polygon_interior
    (vertices : list point) (p : point) : Prop :=
  ~ on_polygon_boundary vertices p /\
  winding_number vertices p <> 0%Z.

Definition interior_lattice_point
    (vertices : list point) (p : point) : Prop :=
  integral_point p /\ in_polygon_interior vertices p.

Definition boundary_lattice_point
    (vertices : list point) (p : point) : Prop :=
  integral_point p /\ on_polygon_boundary vertices p.

Definition has_cardinality {A : Type} (P : A -> Prop) (n : nat) : Prop :=
  exists enumeration : list A,
    NoDup enumeration /\
    length enumeration = n /\
    forall x : A, In x enumeration <-> P x.

Definition edge_cross_product (e : edge) : R :=
  point_x (fst e) * point_y (snd e) -
  point_x (snd e) * point_y (fst e).

Fixpoint signed_double_area (es : list edge) : R :=
  match es with
  | [] => 0
  | e :: rest => edge_cross_product e + signed_double_area rest
  end.

Definition polygon_area (vertices : list point) : R :=
  Rabs (signed_double_area (polygon_edges vertices)) / 2.

Theorem pick_s_theorem :
  forall (vertices : list point) (I B : nat),
    simple_polygon vertices ->
    (forall p : point, In p vertices -> integral_point p) ->
    has_cardinality (interior_lattice_point vertices) I ->
    has_cardinality (boundary_lattice_point vertices) B ->
    polygon_area vertices = INR I + INR B / 2 - 1.
Admitted.
