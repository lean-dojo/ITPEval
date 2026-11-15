(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a4:
  pointwise absolute-value domination between two real quadratic polynomials
  implies the corresponding domination of their discriminants in absolute
  value. This file contains no proof.
*)

let statement =
  `!a b c A B C:real.
     ~(a = &0) /\ ~(A = &0) /\
     (!x:real.
        abs (a * x pow 2 + b * x + c) <=
        abs (A * x pow 2 + B * x + C))
     ==>
     abs (b pow 2 - &4 * a * c) <=
     abs (B pow 2 - &4 * A * C)`;;
