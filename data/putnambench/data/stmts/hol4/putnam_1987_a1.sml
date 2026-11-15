(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_a1:
  four plane curves defined by rational and cubic equations have equal
  pairwise intersections. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;

val putnam_1987_a1 =
  ``!(A B C D : (real # real) set).
      A =
        {p : real # real |
           FST p pow 2 + SND p pow 2 <> 0 /\
           FST p pow 2 - SND p pow 2 =
             FST p / (FST p pow 2 + SND p pow 2)} /\
      B =
        {p : real # real |
           FST p pow 2 + SND p pow 2 <> 0 /\
           2 * FST p * SND p +
             SND p / (FST p pow 2 + SND p pow 2) = 3} /\
      C =
        {p : real # real |
           FST p pow 3 - 3 * FST p * SND p pow 2 + 3 * SND p = 1} /\
      D =
        {p : real # real |
           3 * FST p pow 2 * SND p - 3 * FST p - SND p pow 3 = 0}
      ==>
      A INTER B = C INTER D``;
