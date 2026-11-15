(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_b6:
  a triple of positive natural numbers can reach a zero entry by finitely
  many applications of the prescribed doubling-and-subtraction update.
  This file contains no proof.
*)

let statement =
  `!S:A->num. !f:A->A->(A->num)->A->num.
     (:A) HAS_SIZE 3 /\
     (!i:A. 0 < S i) /\
     (!i j k:A.
        ~(i = j) /\ ~(i = k) /\ ~(j = k)
        ==> !S':A->num.
              if S' i <= S' j then
                (f i j S') i = 2 * S' i /\
                (f i j S') j = S' j - S' i /\
                (f i j S') k = S' k
              else
                f i j S' = S')
     ==>
     ?Ss:num->A->num. ?N:num.
       Ss 0 = S /\
       (?i:A. Ss N i = 0) /\
       (!n:num.
          n < N
          ==> ?i j:A.
                ~(i = j) /\
                f i j (Ss n) = Ss (n + 1))`;;
