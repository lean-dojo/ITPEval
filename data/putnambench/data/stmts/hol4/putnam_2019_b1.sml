(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b1:
  the number of four-point subsets forming squares among integer lattice
  points on circles of squared radii 2^k, together with the origin, is
  5*n + 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory pred_setTheory;

val putnam_2019_b1 =
  ``let lattice_points =
      \n : num.
        {P : int # int |
           P = (0, 0) \/
           ?k : num.
             k <= n /\
             FST P * FST P + SND P * SND P =
             int_of_num (2 EXP k)}
    in
    let squared_distance =
      \P Q : int # int.
        (FST P - FST Q) * (FST P - FST Q) +
        (SND P - SND Q) * (SND P - SND Q)
    in
    let is_square =
      \S : (int # int) set.
        S HAS_SIZE 4 /\
        ?A B C D : int # int.
          S = {A; B; C; D} /\
          squared_distance A B <> 0 /\
          squared_distance A B = squared_distance B C /\
          squared_distance B C = squared_distance C D /\
          squared_distance C D = squared_distance D A /\
          squared_distance A C = squared_distance B D
    in
      !n : num.
        CARD
          {s : (int # int) set |
             s SUBSET lattice_points n /\ is_square s} =
        5 * n + 1``;
