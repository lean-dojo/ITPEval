(* Statement-only formalization of PutnamBench artifact putnam_1979_a4:
   a finite equal red-blue planar point set in general position admits a
   perfect pairing by pairwise disjoint closed segments. This file contains
   no proof. *)

From Stdlib Require Import Reals List.

Open Scope R_scope.

Definition putnam_1979_a4_point := (R * R)%type.
Definition putnam_1979_a4_point_set := putnam_1979_a4_point -> Prop.

Definition putnam_1979_a4_has_cardinality
    {X : Type} (S : X -> Prop) (n : nat) : Prop :=
  exists enumeration : list X,
    NoDup enumeration /\
    length enumeration = n /\
    forall x : X, In x enumeration <-> S x.

Definition putnam_1979_a4_collinear
    (P Q N : putnam_1979_a4_point) : Prop :=
  (fst Q - fst P) * (snd N - snd P) =
  (snd Q - snd P) * (fst N - fst P).

Definition putnam_1979_a4_configuration
    (RB : putnam_1979_a4_point_set * putnam_1979_a4_point_set) : Prop :=
  let (Rset, Bset) := RB in
  exists n : nat,
    putnam_1979_a4_has_cardinality Rset n /\
    putnam_1979_a4_has_cardinality Bset n /\
    (forall P : putnam_1979_a4_point, Rset P -> ~ Bset P) /\
    forall P Q N : putnam_1979_a4_point,
      (Rset P \/ Bset P) ->
      (Rset Q \/ Bset Q) ->
      (Rset N \/ Bset N) ->
      Q <> P ->
      N <> P ->
      N <> Q ->
      ~ putnam_1979_a4_collinear P Q N.

Definition putnam_1979_a4_affine_point
    (P Q : putnam_1979_a4_point) (x : R) : putnam_1979_a4_point :=
  (x * fst P + (1 - x) * fst Q,
   x * snd P + (1 - x) * snd Q).

Definition putnam_1979_a4_matching
    (Rset Bset : putnam_1979_a4_point_set)
    (w :
      (putnam_1979_a4_point * putnam_1979_a4_point) ->
      R -> putnam_1979_a4_point)
    (v :
      (putnam_1979_a4_point * putnam_1979_a4_point) -> Prop) : Prop :=
  exists n : nat,
    putnam_1979_a4_has_cardinality Rset n /\
    putnam_1979_a4_has_cardinality v n /\
    forall L : putnam_1979_a4_point * putnam_1979_a4_point,
      v L ->
      Rset (fst L) /\
      Bset (snd L) /\
      forall M : putnam_1979_a4_point * putnam_1979_a4_point,
        v M ->
        L <> M ->
        fst L <> fst M /\
        snd L <> snd M /\
        forall x y : R,
          0 <= x <= 1 ->
          0 <= y <= 1 ->
          w L x <> w M y.

Definition putnam_1979_a4_solution : Prop := True.

Theorem putnam_1979_a4
    (A :
      (putnam_1979_a4_point_set * putnam_1979_a4_point_set) -> Prop)
    (hA : A = putnam_1979_a4_configuration)
    (w :
      (putnam_1979_a4_point * putnam_1979_a4_point) ->
      R -> putnam_1979_a4_point)
    (hw :
      w =
      fun LP x =>
        putnam_1979_a4_affine_point (fst LP) (snd LP) x) :
  putnam_1979_a4_solution <->
  forall Rset Bset : putnam_1979_a4_point_set,
    A (Rset, Bset) ->
    exists v :
      (putnam_1979_a4_point * putnam_1979_a4_point) -> Prop,
      putnam_1979_a4_matching Rset Bset w v.
Admitted.
