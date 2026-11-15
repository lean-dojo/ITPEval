(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b2:
  every block of ten consecutive integers beginning with a positive integer
  contains a member coprime to every other member. This file contains no proof.
*)

let statement =
  `let S = \n:int. {i:int | n <= i /\ i <= n + &9} in
   !n:int.
     &0 < n
     ==> ?k:int.
           k IN S n /\
           !m:int.
             m IN S n /\ ~(k = m)
             ==> coprime(m,k)`;;
