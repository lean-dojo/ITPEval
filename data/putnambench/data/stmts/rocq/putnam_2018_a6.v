(* Statement-only formalization of PutnamBench corpus artifact putnam_2018_a6:
   rational squared pairwise distances among four planar points with no three
   collinear imply a rational ratio of two triangle areas. This file contains
   no proof. *)

From Stdlib Require Import Reals QArith.

Open Scope R_scope.

Definition putnam_2018_a6_point : Type := (R * R)%type.

Definition putnam_2018_a6_squared_distance
    (p q : putnam_2018_a6_point) : R :=
  (fst p - fst q) ^ 2 + (snd p - snd q) ^ 2.

Definition putnam_2018_a6_rational_squared_distance
    (p q : putnam_2018_a6_point) : Prop :=
  p <> q /\
  exists r : Q, putnam_2018_a6_squared_distance p q = Q2R r.

Definition putnam_2018_a6_signed_twice_area
    (a b c : putnam_2018_a6_point) : R :=
  (fst b - fst a) * (snd c - snd a) -
  (snd b - snd a) * (fst c - fst a).

Definition putnam_2018_a6_noncollinear
    (a b c : putnam_2018_a6_point) : Prop :=
  putnam_2018_a6_signed_twice_area a b c <> 0.

Definition putnam_2018_a6_triangle_area
    (a b c : putnam_2018_a6_point) : R :=
  Rabs (putnam_2018_a6_signed_twice_area a b c) / 2.

Theorem putnam_2018_a6
    (A B C D : putnam_2018_a6_point)
    (ABCDnoline :
      putnam_2018_a6_noncollinear A B C /\
      putnam_2018_a6_noncollinear A B D /\
      putnam_2018_a6_noncollinear A C D /\
      putnam_2018_a6_noncollinear B C D)
    (ABCDsqrrat :
      putnam_2018_a6_rational_squared_distance A B /\
      putnam_2018_a6_rational_squared_distance A C /\
      putnam_2018_a6_rational_squared_distance A D /\
      putnam_2018_a6_rational_squared_distance B C /\
      putnam_2018_a6_rational_squared_distance B D /\
      putnam_2018_a6_rational_squared_distance C D) :
  exists q : Q,
    putnam_2018_a6_triangle_area A B C /
    putnam_2018_a6_triangle_area A B D = Q2R q.
Admitted.
