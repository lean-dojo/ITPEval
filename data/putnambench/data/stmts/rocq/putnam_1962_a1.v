(* Statement-only formalization of PutnamBench artifact putnam_1962_a1:
   among five planar points with no three collinear, four are the vertices
   of a convex quadrilateral. This file contains no proof. *)

From Stdlib Require Import Reals List.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition subset (A B : point_set) : Prop :=
  forall x : point, A x -> B x.

Definition singleton (a : point) : point_set :=
  fun x => x = a.

Definition set_difference (A B : point_set) : point_set :=
  fun x => A x /\ ~ B x.

Definition has_cardinality (A : point_set) (n : nat) : Prop :=
  exists enumeration : list point,
    NoDup enumeration /\
    length enumeration = n /\
    forall x : point, In x enumeration <-> A x.

Definition affine_combination
    (lambda : R) (a b : point) : point :=
  ((1 - lambda) * fst a + lambda * fst b,
   (1 - lambda) * snd a + lambda * snd b).

Definition convex (A : point_set) : Prop :=
  forall (a b : point) (lambda : R),
    A a ->
    A b ->
    0 <= lambda <= 1 ->
    A (affine_combination lambda a b).

Definition convex_hull (A : point_set) : point_set :=
  fun x =>
    forall C : point_set,
      convex C ->
      subset A C ->
      C x.

Definition collinear_points (a b c : point) : Prop :=
  (fst b - fst a) * (snd c - snd a) =
  (snd b - snd a) * (fst c - fst a).

Definition collinear (A : point_set) : Prop :=
  forall a b c : point,
    A a ->
    A b ->
    A c ->
    collinear_points a b c.

Theorem putnam_1962_a1 :
  forall S : point_set,
    has_cardinality S 5%nat ->
    (forall s : point_set,
      subset s S ->
      has_cardinality s 3%nat ->
      ~ collinear s) ->
    exists T : point_set,
      subset T S /\
      has_cardinality T 4%nat /\
      ~ exists t : point,
        T t /\
        convex_hull (set_difference T (singleton t)) t.
Admitted.
