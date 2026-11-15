(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b3:
  the positive integers where the second difference of the number of
  average-closed subsets of an integer interval equals one. This file
  contains no proof.
*)

let statement =
  `let mediocre =
     \(n:int) (S:int->bool).
       S SUBSET {x:int | &1 <= x /\ x <= n} /\
       (!a b c:int.
          a IN S /\ b IN S /\ a + b = &2 * c
          ==> c IN S) in
   let A =
     \n:int. (&(CARD {S:int->bool | mediocre n S}):int) in
   {n:int |
      &0 < n /\
      A (n + &2) - &2 * A (n + &1) + A n = &1} =
   {n:int |
      ?k:num. 1 <= k /\ n = (&2:int) pow k - &1}`;;
