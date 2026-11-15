(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_a4:
  the count of n by n matrices with entries in {-1,0,1} whose transversal
  sums are all equal, together with its closed formula. This file contains no
  proof.
*)

let statement =
  `let admissible_matrix =
     \n:num. \A:num->num->int.
       (!i j:num.
          i < n /\ j < n
          ==> A i j = --(&1:int) \/ A i j = &0 \/ A i j = &1) /\
       (!i j:num.
          ~(i < n /\ j < n)
          ==> A i j = &0) /\
       (?S:int.
          !p:num->num.
            BIJ p (0..n-1) (0..n-1)
            ==> isum (0..n-1) (\i. A i (p i)) = S) in
   let f =
     \n:num.
       CARD {A:num->num->int | admissible_matrix n A} in
   !n:num.
     0 < n
     ==> (&(f n):int) =
         (&4:int) pow n +
         &2 * ((&3:int) pow n) -
         &4 * ((&2:int) pow n) +
         &1`;;
