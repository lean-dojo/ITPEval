(* Statement-only formalization of hundred-theorems__rocq__050,
   "The Number of Platonic Solids": full-dimensional real three-dimensional
   polytopes with constant numbers of edges per facet and at each vertex have
   exactly the five Platonic incidence pairs. This file contains no proof. *)

From Stdlib Require Import Reals List.

Import ListNotations.
Open Scope R_scope.

Definition point := (R * (R * R))%type.

Definition point_zero : point := (0, (0, 0)).

Definition point_add (u v : point) : point :=
  (fst u + fst v,
   (fst (snd u) + fst (snd v), snd (snd u) + snd (snd v))).

Definition point_scale (a : R) (u : point) : point :=
  (a * fst u, (a * fst (snd u), a * snd (snd u))).

Definition point_dot (u v : point) : R :=
  fst u * fst v +
  fst (snd u) * fst (snd v) +
  snd (snd u) * snd (snd v).

Fixpoint sum_reals (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + sum_reals rest
  end.

Fixpoint linear_combination (weights : list R) (vertices : list point)
    : point :=
  match weights, vertices with
  | w :: ws, v :: vs =>
      point_add (point_scale w v) (linear_combination ws vs)
  | _, _ => point_zero
  end.

Definition convex_hull (vertices : list point) : point -> Prop :=
  fun x =>
    exists weights : list R,
      length weights = length vertices /\
      Forall (fun w => 0 <= w) weights /\
      sum_reals weights = 1 /\
      linear_combination weights vertices = x.

Definition subset (s t : point -> Prop) : Prop :=
  forall x, s x -> t x.

Definition same_set (s t : point -> Prop) : Prop :=
  forall x, s x <-> t x.

Fixpoint pairwise_distinct_sets (sets : list (point -> Prop)) : Prop :=
  match sets with
  | [] => True
  | s :: rest =>
      (forall t, In t rest -> ~ same_set s t) /\
      pairwise_distinct_sets rest
  end.

Definition has_cardinality
    (collection : (point -> Prop) -> Prop) (n : nat) : Prop :=
  exists representatives : list (point -> Prop),
    length representatives = n /\
    (forall s,
      collection s <->
      exists t, In t representatives /\ same_set s t) /\
    pairwise_distinct_sets representatives.

Definition affine_dimension_zero (s : point -> Prop) : Prop :=
  exists a, s a /\ forall x, s x -> x = a.

Definition affine_dimension_at_most_one (s : point -> Prop) : Prop :=
  exists a direction,
    (exists x, s x) /\
    forall x, s x ->
      exists parameter : R,
        x = point_add a (point_scale parameter direction).

Definition affine_dimension_one (s : point -> Prop) : Prop :=
  affine_dimension_at_most_one s /\ ~ affine_dimension_zero s.

Definition affine_dimension_at_most_two (s : point -> Prop) : Prop :=
  exists normal offset,
    normal <> point_zero /\
    (exists x, s x) /\
    forall x, s x -> point_dot normal x = offset.

Definition affine_dimension_two (s : point -> Prop) : Prop :=
  affine_dimension_at_most_two s /\
  ~ affine_dimension_at_most_one s.

Definition full_dimensional_three (s : point -> Prop) : Prop :=
  (exists x, s x) /\ ~ affine_dimension_at_most_two s.

Definition face_of (polytope face : point -> Prop) : Prop :=
  exists normal offset,
    (forall x, polytope x -> point_dot normal x <= offset) /\
    (forall x,
      face x <-> polytope x /\ point_dot normal x = offset).

Definition edge_in_facet
    (polytope facet edge : point -> Prop) : Prop :=
  face_of polytope edge /\
  affine_dimension_one edge /\
  subset edge facet.

Definition edge_at_vertex
    (polytope vertex edge : point -> Prop) : Prop :=
  face_of polytope edge /\
  affine_dimension_one edge /\
  subset vertex edge.

Theorem number_of_platonic_solids :
  forall m n : nat,
    (exists vertices : list point,
      let polytope := convex_hull vertices in
      full_dimensional_three polytope /\
      (forall facet,
        face_of polytope facet ->
        affine_dimension_two facet ->
        has_cardinality (edge_in_facet polytope facet) m) /\
      (forall vertex,
        face_of polytope vertex ->
        affine_dimension_zero vertex ->
        has_cardinality (edge_at_vertex polytope vertex) n)) <->
    (m = 3%nat /\ n = 3%nat) \/
    (m = 4%nat /\ n = 3%nat) \/
    (m = 3%nat /\ n = 4%nat) \/
    (m = 5%nat /\ n = 3%nat) \/
    (m = 3%nat /\ n = 5%nat).
Admitted.
