(* Statement-only formalization of PutnamBench artifact putnam_1987_a1:
   equality of the intersections of four real plane curves defined by
   polynomial and reciprocal equations. This file contains no proof. *)

From Stdlib Require Import Reals Ensembles.

Open Scope R_scope.

Definition putnam_1987_a1_point : Type := (R * R)%type.

Theorem putnam_1987_a1
    (A B C D : Ensemble putnam_1987_a1_point)
    (hA :
      Same_set putnam_1987_a1_point A
        (fun p : putnam_1987_a1_point =>
          fst p ^ 2 + snd p ^ 2 <> 0 /\
          fst p ^ 2 - snd p ^ 2 =
            fst p / (fst p ^ 2 + snd p ^ 2)))
    (hB :
      Same_set putnam_1987_a1_point B
        (fun p : putnam_1987_a1_point =>
          fst p ^ 2 + snd p ^ 2 <> 0 /\
          2 * fst p * snd p +
            snd p / (fst p ^ 2 + snd p ^ 2) = 3))
    (hC :
      Same_set putnam_1987_a1_point C
        (fun p : putnam_1987_a1_point =>
          fst p ^ 3 - 3 * fst p * snd p ^ 2 + 3 * snd p = 1))
    (hD :
      Same_set putnam_1987_a1_point D
        (fun p : putnam_1987_a1_point =>
          3 * fst p ^ 2 * snd p - 3 * fst p - snd p ^ 3 = 0)) :
  Same_set putnam_1987_a1_point
    (Intersection putnam_1987_a1_point A B)
    (Intersection putnam_1987_a1_point C D).
Admitted.
