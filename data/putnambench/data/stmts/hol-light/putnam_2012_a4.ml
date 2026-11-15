(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a4:
  integer points selected by two real intervals form a finite arithmetic
  progression when the product of the interval lengths is small enough.
  This file contains no proof.
*)

let statement =
  `let finite_arithmetic_progression =
     \s:int->bool.
       ?n:num. ?a d:int.
         (&0:int) < d /\
         s =
         {x:int |
            ?i:num.
              i < n /\ x = a + (&i:int) * d} in
   !q r:int. !A B:real#real. !T S:int->bool.
     (&0:int) < q /\
     FST A < SND A /\
     FST B < SND B /\
     T =
       {x:int |
          ?b m:int.
            FST B <= real_of_int b /\
            real_of_int b <= SND B /\
            x = b + m * q} /\
     S =
       {a:int |
          FST A <= real_of_int a /\
          real_of_int a <= SND A /\
          r * a IN T} /\
     (SND A - FST A) * (SND B - FST B) < real_of_int q
     ==>
     finite_arithmetic_progression
       {x:int |
          x IN S /\
          FST A <= real_of_int x /\
          real_of_int x <= SND A}`;;
