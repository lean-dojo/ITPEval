(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_a6:
  an integer-coefficient polynomial iterated from zero can return to zero at
  a positive time only if its first or second iterate is zero. This file
  contains no proof.
*)

let statement =
  `let eval =
     \p:int list. \x:int.
       ITLIST (\c acc. c + x * acc) p (&0) in
   !f:int list. !a:num->int.
     a 0 = &0 /\
     (!n:num. a (n + 1) = eval f (a n))
     ==>
     ((?m:num. 0 < m /\ a m = &0)
      ==> a 1 = &0 \/ a 2 = &0)`;;
