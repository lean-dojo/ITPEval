(* Statement-only formalization of PutnamBench corpus artifact putnam_2017_b1:
   the intersection criterion for two distinct affine lines in the real plane
   via prescribed nonzero scalar multiples of displacement vectors. This file
   contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2017_b1_point : Type := (R * R)%type.
Definition putnam_2017_b1_point_set : Type :=
  putnam_2017_b1_point -> Prop.

Definition putnam_2017_b1_point_zero : putnam_2017_b1_point :=
  (0, 0).

Definition putnam_2017_b1_point_add
    (p q : putnam_2017_b1_point) : putnam_2017_b1_point :=
  (fst p + fst q, snd p + snd q).

Definition putnam_2017_b1_point_sub
    (p q : putnam_2017_b1_point) : putnam_2017_b1_point :=
  (fst p - fst q, snd p - snd q).

Definition putnam_2017_b1_point_scale
    (a : R) (p : putnam_2017_b1_point) : putnam_2017_b1_point :=
  (a * fst p, a * snd p).

Definition putnam_2017_b1_affine_line
    (L : putnam_2017_b1_point_set) : Prop :=
  exists v w : putnam_2017_b1_point,
    w <> putnam_2017_b1_point_zero /\
    forall p : putnam_2017_b1_point,
      L p <->
      exists t : R,
        p =
          putnam_2017_b1_point_add
            v (putnam_2017_b1_point_scale t w).

Theorem putnam_2017_b1
    (lines : putnam_2017_b1_point_set -> Prop)
    (L1 L2 : putnam_2017_b1_point_set)
    (L1L2lines : lines L1 /\ lines L2)
    (L1L2distinct :
      ~ forall p : putnam_2017_b1_point, L1 p <-> L2 p)
    (hlines :
      forall L : putnam_2017_b1_point_set,
        lines L <-> putnam_2017_b1_affine_line L) :
  (exists p : putnam_2017_b1_point, L1 p /\ L2 p) <->
  forall lambda : R,
    lambda <> 0 ->
    forall P : putnam_2017_b1_point,
      (~ L1 P /\ ~ L2 P) ->
      exists A1 A2 : putnam_2017_b1_point,
        L1 A1 /\
        L2 A2 /\
        putnam_2017_b1_point_sub A2 P =
          putnam_2017_b1_point_scale
            lambda (putnam_2017_b1_point_sub A1 P).
Admitted.
