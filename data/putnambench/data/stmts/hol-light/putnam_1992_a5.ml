(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_a5:
  nonexistence of three consecutive equal blocks in the binary digit-parity
  sequence. This file contains no proof.
*)

let statement =
  `let num1s =
     \n:num. CARD {i:num | ODD (n DIV (2 EXP i))} in
   let a =
     \n:num. if EVEN (num1s n) then 0 else 1 in
   ~(?k m:num.
       0 < k /\
       0 < m /\
       !j:num.
         j <= m - 1
         ==> a (k + j) = a (k + m + j) /\
             a (k + m + j) = a (k + 2 * m + j))`;;
