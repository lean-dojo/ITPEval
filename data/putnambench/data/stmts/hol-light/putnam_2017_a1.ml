(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_a1
  (putnambench__hol-light__putnam_2017_a1): characterization of the positive
  integers omitted by the least set closed under the stated square and
  shifted-square conditions. This file contains no proof.
*)

let statement =
  `let is_qualifying =
     \S:int->bool.
       (!n:int. n IN S ==> &0 < n) /\
       (&2:int) IN S /\
       (!n:int. &0 < n /\ n pow 2 IN S ==> n IN S) /\
       (!n:int. n IN S ==> (n + &5) pow 2 IN S) in
   let putnam_2017_a1_solution =
     {x:int | &0 < x /\ (x = &1 \/ (&5:int) divides x)} in
   !S:int->bool.
     is_qualifying S /\
     (!A:int->bool. is_qualifying A ==> S SUBSET A)
     ==> {x:int | &0 < x /\ ~(x IN S)} =
         putnam_2017_a1_solution`;;
