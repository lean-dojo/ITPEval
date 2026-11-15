(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a4:
  integers selected from a real interval by a modular condition determined by
  a second interval form a finite arithmetic progression when the product of
  the interval lengths is less than the positive modulus. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory pred_setTheory realTheory
     intrealTheory;

val putnam_2012_a4 =
  ``!q r : int. !A B : real # real.
      0 < q /\
      FST A < SND A /\
      FST B < SND B /\
      (SND A - FST A) * (SND B - FST B) < real_of_int q
      ==>
      let T =
        {x : int |
           ?b m : int.
             FST B <= real_of_int b /\
             real_of_int b <= SND B /\
             x = b + m * q}
      in
        let S =
          {a : int |
             FST A <= real_of_int a /\
             real_of_int a <= SND A /\
             r * a IN T}
        in
          ?n : num. ?a d : int.
            0 < d /\
            {x : int |
               x IN S /\
               FST A <= real_of_int x /\
               real_of_int x <= SND A} =
              IMAGE
                (\i : num. a + int_of_num i * d)
                (count n)``;
