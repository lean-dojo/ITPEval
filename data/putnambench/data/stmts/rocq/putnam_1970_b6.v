(* Statement-only formalization of PutnamBench artifact putnam_1970_b6:
   a nondegenerate ordered quadrilateral tangent to an inscribed circle and
   having area equal to the square root of the product of its side lengths is
   cyclic. This file contains no proof. *)

From Stdlib Require Import Reals List.

Open Scope R_scope.

Inductive index4 : Type :=
| index0
| index1
| index2
| index3.

Definition next_index (i : index4) : index4 :=
  match i with
  | index0 => index1
  | index1 => index2
  | index2 => index3
  | index3 => index0
  end.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition point_distance (p q : point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition point_affine_combination
    (t : R) (p q : point) : point :=
  ((1 - t) * fst p + t * fst q,
   (1 - t) * snd p + t * snd q).

Definition subset (A B : point_set) : Prop :=
  forall p : point, A p -> B p.

Definition same_set (A B : point_set) : Prop :=
  forall p : point, A p <-> B p.

Definition convex (A : point_set) : Prop :=
  forall (p q : point) (t : R),
    A p ->
    A q ->
    0 <= t <= 1 ->
    A (point_affine_combination t p q).

Definition convex_hull (A : point_set) : point_set :=
  fun p : point =>
    forall C : point_set,
      convex C ->
      subset A C ->
      C p.

Definition interior (A : point_set) : point_set :=
  fun p : point =>
    exists epsilon : R,
      0 < epsilon /\
      forall q : point,
        point_distance q p < epsilon ->
        A q.

Definition closed_segment (p q : point) : point_set :=
  fun x : point =>
    exists t : R,
      0 <= t <= 1 /\
      x = point_affine_combination t p q.

Definition collinear_points (p q r : point) : Prop :=
  (fst q - fst p) * (snd r - snd p) =
  (snd q - snd p) * (fst r - fst p).

Definition collinear (A : point_set) : Prop :=
  forall p q r : point,
    A p ->
    A q ->
    A r ->
    collinear_points p q r.

Definition vertex_set (L : index4 -> point) : point_set :=
  fun p : point => exists i : index4, p = L i.

Definition has_cardinality (A : point_set) (n : nat) : Prop :=
  exists enumeration : list point,
    NoDup enumeration /\
    length enumeration = n /\
    forall p : point, In p enumeration <-> A p.

Record open_rectangle : Type := {
  rectangle_x_lower : R;
  rectangle_x_upper : R;
  rectangle_y_lower : R;
  rectangle_y_upper : R
}.

Definition in_open_rectangle
    (rectangle : open_rectangle) (p : point) : Prop :=
  rectangle_x_lower rectangle < fst p <
    rectangle_x_upper rectangle /\
  rectangle_y_lower rectangle < snd p <
    rectangle_y_upper rectangle.

Definition rectangle_area (rectangle : open_rectangle) : R :=
  Rmax 0
    (rectangle_x_upper rectangle - rectangle_x_lower rectangle) *
  Rmax 0
    (rectangle_y_upper rectangle - rectangle_y_lower rectangle).

Definition rectangles_cover
    (A : point_set) (rectangles : nat -> open_rectangle) : Prop :=
  forall p : point,
    A p ->
    exists n : nat, in_open_rectangle (rectangles n) p.

Fixpoint partial_rectangle_area
    (rectangles : nat -> open_rectangle) (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      partial_rectangle_area rectangles k +
      rectangle_area (rectangles k)
  end.

(* This is the countable-open-rectangle characterization of planar Lebesgue
   outer measure. On a finite convex hull it equals planar Lebesgue measure. *)
Definition has_planar_lebesgue_measure
    (A : point_set) (area : R) : Prop :=
  0 <= area /\
  (forall rectangles : nat -> open_rectangle,
    rectangles_cover A rectangles ->
    forall lower : R,
      lower < area ->
      exists n : nat,
        lower < partial_rectangle_area rectangles n) /\
  (forall epsilon : R,
    0 < epsilon ->
    exists rectangles : nat -> open_rectangle,
      rectangles_cover A rectangles /\
      forall n : nat,
        partial_rectangle_area rectangles n < area + epsilon).

Theorem putnam_1970_b6
    (L : index4 -> point)
    (S : point_set)
    (S_def : same_set S (vertex_set L))
    (hSquad :
      has_cardinality S 4%nat /\
      forall s : point_set,
        subset s S ->
        has_cardinality s 3%nat ->
        ~ collinear s)
    (hlens :
      0 < point_distance (L index0) (L index1) /\
      0 < point_distance (L index1) (L index2) /\
      0 < point_distance (L index2) (L index3) /\
      0 < point_distance (L index3) (L index0))
    (horder :
      forall (i : index4) (p : point),
        closed_segment (L i) (L (next_index i)) p ->
        ~ interior (convex_hull S) p)
    (hcircum :
      exists (center : point) (radius : R),
        convex_hull S center /\
        0 < radius /\
        forall i : index4,
          exists! tangent : point,
            collinear_points
              tangent (L i) (L (next_index i)) /\
            point_distance center tangent = radius)
    (harea :
      has_planar_lebesgue_measure
        (convex_hull S)
        (sqrt
          (point_distance (L index0) (L index1) *
           point_distance (L index1) (L index2) *
           point_distance (L index2) (L index3) *
           point_distance (L index3) (L index0)))) :
  exists (center : point) (radius : R),
    forall p : point,
      S p ->
      point_distance p center = radius.
Admitted.
