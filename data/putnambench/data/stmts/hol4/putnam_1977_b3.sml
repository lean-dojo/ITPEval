(*
  Statement-only formalization of PutnamBench artifact putnam_1977_b3:
  whether iterating the coordinatewise doubling balancing act on every
  positive irrational real triple summing to one eventually makes all three
  coordinates less than one half. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_of_ratTheory;

val putnam_1977_b3 =
  ``let P =
      \w : real # (real # real).
        FST w NOTIN q_set /\
        FST (SND w) NOTIN q_set /\
        SND (SND w) NOTIN q_set /\
        0 < FST w /\
        0 < FST (SND w) /\
        0 < SND (SND w) /\
        FST w + FST (SND w) + SND (SND w) = 1
    in
    let balanced =
      \w : real # (real # real).
        FST w < 1 / 2 /\
        FST (SND w) < 1 / 2 /\
        SND (SND w) < 1 / 2
    in
    let B =
      \w : real # (real # real).
        (if FST w > 1 / 2 then 2 * FST w - 1 else 2 * FST w,
         (if FST (SND w) > 1 / 2
          then 2 * FST (SND w) - 1
          else 2 * FST (SND w),
          if SND (SND w) > 1 / 2
          then 2 * SND (SND w) - 1
          else 2 * SND (SND w)))
    in
    let putnam_1977_b3_solution = F
    in
      ((!t : real # (real # real).
          P t ==> ?n : num. balanced (FUNPOW B n t))
       <=>
       putnam_1977_b3_solution)``;
