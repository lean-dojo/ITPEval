(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a6:
  the largest size of two families of real square matrices whose cross-products
  have a zero diagonal entry exactly for unequal family indices. This file
  contains no proof.
*)

let statement =
  `let matrix_mul =
     \(A:real^N^N) (B:real^N^N).
       (lambda i j.
          sum (1..dimindex(:N)) (\p. A$i$p * B$p$j)):real^N^N in
   let admissible =
     \k:num.
       ?M:num->real^N^N.
         ?N:num->real^N^N.
         !i:num. !j:num.
           i < k /\ j < k
           ==>
           ((?p:num.
               1 <= p /\ p <= dimindex(:N) /\
               (matrix_mul (M i) (N j))$p$p = &0) <=>
            ~(i = j)) in
   !n:num.
     0 < n /\ dimindex(:N) = n
     ==>
     1 <= n EXP n /\
     admissible (n EXP n) /\
     (!k:num. 1 <= k /\ admissible k ==> k <= n EXP n)`;;
