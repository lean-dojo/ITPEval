(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b4:
  rationality of the product of two roots of an integer-coefficient real
  quartic when their sum is rational and differs from the other roots' sum.
  This file contains no proof.
*)

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   !f:real->real.
   !a b c d e:int.
   !r1 r2 r3 r4:real.
     ~(a = &0) /\
     (!z:real.
        f z =
        real_of_int a * z pow 4 +
        real_of_int b * z pow 3 +
        real_of_int c * z pow 2 +
        real_of_int d * z +
        real_of_int e) /\
     (!z:real.
        f z =
        real_of_int a *
        (z - r1) * (z - r2) * (z - r3) * (z - r4))
     ==>
     (is_rational (r1 + r2) /\ ~(r1 + r2 = r3 + r4)
      ==> is_rational (r1 * r2))`;;
