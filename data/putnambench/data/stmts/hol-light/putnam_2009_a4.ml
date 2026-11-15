(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_a4:
  whether the rational numbers are forced by containing zero and closure under
  shifts by one and the specified reciprocal operation, with answer false.
  This file contains no proof.
*)

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   let putnam_2009_a4_solution = F in
   ((!S:real->bool.
       S SUBSET {x:real | is_rational x} /\
       &0 IN S /\
       (!x:real.
          x IN S
          ==> x + &1 IN S /\ x - &1 IN S) /\
       (!x:real.
          x IN S /\ ~(x = &0) /\ ~(x = &1)
          ==> &1 / (x * (x - &1)) IN S)
       ==> !r:real. is_rational r ==> r IN S)
    <=> putnam_2009_a4_solution)`;;
