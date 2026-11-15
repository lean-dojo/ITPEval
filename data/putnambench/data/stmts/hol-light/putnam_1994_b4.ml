(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b4:
  the greatest common divisor of the entries of A^n minus the identity tends
  to infinity for A = ((3,2),(4,3)). This file contains no proof.
*)

let statement =
  `let matrix_mul =
     \M N:((int#int)#(int#int)).
       (((FST (FST M) * FST (FST N) +
          SND (FST M) * FST (SND N)),
         (FST (FST M) * SND (FST N) +
          SND (FST M) * SND (SND N))),
        ((FST (SND M) * FST (FST N) +
          SND (SND M) * FST (SND N)),
         (FST (SND M) * SND (FST N) +
          SND (SND M) * SND (SND N)))) in
   let matrix_sub =
     \M N:((int#int)#(int#int)).
       (((FST (FST M) - FST (FST N)),
         (SND (FST M) - SND (FST N))),
        ((FST (SND M) - FST (SND N)),
         (SND (SND M) - SND (SND N)))) in
   let matrix_gcd =
     \M:((int#int)#(int#int)).
       gcd
         (gcd
            (gcd (num_of_int (abs (FST (FST M))),
                  num_of_int (abs (SND (FST M)))),
             num_of_int (abs (FST (SND M)))),
          num_of_int (abs (SND (SND M)))) in
   let a_matrix:((int#int)#(int#int)) = ((&3,&2),(&4,&3)) in
   let identity:((int#int)#(int#int)) = ((&1,&0),(&0,&1)) in
   !matpow:num->((int#int)#(int#int)). !d:num->num.
     matpow 0 = identity /\
     (!n:num. matpow (SUC n) = matrix_mul (matpow n) a_matrix) /\
     (!n:num.
        1 <= n
        ==> d n = matrix_gcd (matrix_sub (matpow n) identity))
     ==> !k:num. ?N:num. !n:num. N <= n ==> k <= d n`;;
