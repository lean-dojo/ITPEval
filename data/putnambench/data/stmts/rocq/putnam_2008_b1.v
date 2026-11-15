(* Statement-only formalization of PutnamBench corpus artifact putnam_2008_b1:
   the maximum number of rational-coordinate points on a real plane circle
   with a non-rational center is two. This file contains no proof. *)

From Stdlib Require Import Reals QArith Lists.List.

Open Scope R_scope.

Definition putnam_2008_b1_point : Type := (R * R)%type.

Definition putnam_2008_b1_distance
    (p q : putnam_2008_b1_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_2008_b1_rational_point
    (p : putnam_2008_b1_point) : Prop :=
  exists x y : Q,
    fst p = Q2R x /\
    snd p = Q2R y.

Definition putnam_2008_b1_on_circle
    (center p : putnam_2008_b1_point) (radius : R) : Prop :=
  putnam_2008_b1_distance p center = radius.

Definition putnam_2008_b1_has_cardinality
    {A : Type} (P : A -> Prop) (cardinality : nat) : Prop :=
  exists enumeration : list A,
    NoDup enumeration /\
    length enumeration = cardinality /\
    forall x : A, In x enumeration <-> P x.

Definition putnam_2008_b1_possible_count (n : nat) : Prop :=
  exists (center : putnam_2008_b1_point) (radius : R),
    ~ putnam_2008_b1_rational_point center /\
    putnam_2008_b1_has_cardinality
      (fun p : putnam_2008_b1_point =>
        putnam_2008_b1_on_circle center p radius /\
        putnam_2008_b1_rational_point p)
      n.

Definition putnam_2008_b1_is_greatest
    (values : nat -> Prop) (maximum : nat) : Prop :=
  values maximum /\
  forall value : nat, values value -> (value <= maximum)%nat.

Definition putnam_2008_b1_solution : nat := 2%nat.

Theorem putnam_2008_b1 :
  putnam_2008_b1_is_greatest
    putnam_2008_b1_possible_count
    putnam_2008_b1_solution.
Admitted.
