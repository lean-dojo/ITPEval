(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a5:
  parity classification of the number of positive integers below one quarter
  of an odd positive integer q that are coprime to q. This file contains no
  proof.
*)

let statement =
  `!q Nq:num.
     ODD q /\
     0 < q /\
     Nq = CARD {a:num | 0 < a /\ 4 * a < q /\ coprime(a,q)}
     ==>
     (ODD Nq <=>
      ?p k:num.
        q = p EXP k /\
        0 < k /\
        prime p /\
        (p MOD 8 = 5 \/ p MOD 8 = 7))`;;
