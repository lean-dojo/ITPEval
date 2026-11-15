(* Statement-only formalization of PutnamBench artifact putnam_1967_b1:
   six cyclically ordered points on a circle, with three alternating chords
   equal to the radius, have opposite-side midpoints forming an equilateral
   triangle. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition point_distance (a b : point) : R :=
  sqrt ((fst a - fst b) ^ 2 + (snd a - snd b) ^ 2).

Definition midpoint (a b : point) : point :=
  ((fst a + fst b) / 2, (snd a + snd b) / 2).

Definition affine_combination (t : R) (a b : point) : point :=
  ((1 - t) * fst a + t * fst b,
   (1 - t) * snd a + t * snd b).

Definition closed_segment (a b : point) : point_set :=
  fun p : point =>
    exists t : R,
      0 <= t <= 1 /\
      p = affine_combination t a b.

Definition subset (A B : point_set) : Prop :=
  forall p : point, A p -> B p.

Definition convex (A : point_set) : Prop :=
  forall (a b : point) (t : R),
    A a ->
    A b ->
    0 <= t <= 1 ->
    A (affine_combination t a b).

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

Inductive index6 : Type :=
| I0 | I1 | I2 | I3 | I4 | I5.

Definition next6 (i : index6) : index6 :=
  match i with
  | I0 => I1
  | I1 => I2
  | I2 => I3
  | I3 => I4
  | I4 => I5
  | I5 => I0
  end.

Definition vertex_set (L : index6 -> point) : point_set :=
  fun p : point =>
    exists i : index6, L i = p.

Theorem putnam_1967_b1
    (r : R)
    (L : index6 -> point)
    (P Q Rpt : point)
    (hP : P = midpoint (L I1) (L I2))
    (hQ : Q = midpoint (L I3) (L I4))
    (hR : Rpt = midpoint (L I5) (L I0))
    (hr : r > 0)
    (hcyclic :
      exists O : point,
        forall i : index6, point_distance O (L i) = r)
    (horder :
      forall i j : index6,
        i <> j ->
        next6 i = j \/
        i = next6 j \/
        exists p : point,
          closed_segment (L i) (L j) p /\
          interior (convex_hull (vertex_set L)) p)
    (hlens :
      point_distance (L I0) (L I1) = r /\
      point_distance (L I2) (L I3) = r /\
      point_distance (L I4) (L I5) = r)
    (hdist :
      L I1 <> L I2 /\
      L I3 <> L I4 /\
      L I5 <> L I0) :
  point_distance P Q = point_distance Rpt P /\
  point_distance Q Rpt = point_distance P Q.
Admitted.
