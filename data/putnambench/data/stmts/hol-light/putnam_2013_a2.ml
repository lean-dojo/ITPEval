(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_a2:
  injectivity on the positive nonsquare integers of the minimum possible last
  entry in a strictly increasing integer list whose product with the initial
  integer is a perfect square. This file contains no proof.
*)

let statement =
  `let S =
     {n:int | (&0:int) < n /\ ~(?m:int. m pow 2 = n)} in
   let P =
     \(n:int) (a:int list).
       0 < LENGTH a /\
       n < EL 0 a /\
       (?m:int.
          m pow 2 =
          n * ITLIST (\x acc. x * acc) a (&1:int)) /\
       (!i:num.
          i + 1 < LENGTH a
          ==> EL i a < EL (i + 1) a) in
   let T =
     \(n:int).
       {r:int |
          ?a:int list.
            P n a /\ LAST a = r} in
   !f:int->int.
     (!n:int.
        n IN S
        ==>
        f n IN T n /\
        (!r:int. r IN T n ==> f n <= r))
     ==>
     !x y:int.
       x IN S /\ y IN S /\ f x = f y
       ==> x = y`;;
