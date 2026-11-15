(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_b4:
  the positive fixed point of x = 2207 - 1/x has one-eighth power
  (3 + sqrt 5)/2. This file contains no proof.
*)

let statement =
  `let putnam_1995_b4_solution = (&3:int,&1:int,&5:int,&2:int) in
   let a = FST putnam_1995_b4_solution in
   let b = FST (SND putnam_1995_b4_solution) in
   let c = FST (SND (SND putnam_1995_b4_solution)) in
   let d = SND (SND (SND putnam_1995_b4_solution)) in
   !contfrac:real.
     contfrac = &2207 - &1 / contfrac /\
     &1 < contfrac
     ==>
     sqrt (sqrt (sqrt contfrac)) =
     (real_of_int a + real_of_int b * sqrt (real_of_int c)) /
     real_of_int d`;;
