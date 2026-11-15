(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b2:
  classification of the real parameters for which a line intersects the given
  quartic curve in four distinct points. This file contains no proof.
*)

let statement =
  `!c:real.
     (?m b:real.
        {x:real |
           m * x + b =
           x pow 4 + &9 * x pow 3 + c * x pow 2 + &9 * x + &4}
        HAS_SIZE 4)
     <=>
     c < &243 / &8`;;
