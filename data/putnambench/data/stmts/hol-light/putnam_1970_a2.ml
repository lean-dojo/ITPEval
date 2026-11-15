(*
  Statement-only formalization of PutnamBench artifact putnam_1970_a2:
  under a negative quadratic discriminant, a real bivariate polynomial with
  quadratic and cubic terms has no nonzero zeros sufficiently near the origin.
  This file contains no proof.
*)

let statement =
  `!A B C D E F G:real.
     B pow 2 - &4 * A * C < &0
     ==> ?delta:real.
           &0 < delta /\
           ~(?x y:real.
               ~(x pow 2 + y pow 2 = &0) /\
               x pow 2 + y pow 2 < delta pow 2 /\
               A * x pow 2 + B * x * y + C * y pow 2 +
               D * x pow 3 + E * x pow 2 * y +
               F * x * y pow 2 + G * y pow 3 = &0)`;;
