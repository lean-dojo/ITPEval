(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b4:
  every set of m*n+1 positive natural numbers contains either an
  (m+1)-element divisibility antichain or an (n+1)-element subset in which
  every smaller member divides every larger member. This file contains no
  proof.
*)

let statement =
  `!m n:num. !S:num->bool.
     S HAS_SIZE (m * n + 1) /\
     (!i:num. i IN S ==> 0 < i)
     ==> ?T.
           T SUBSET S /\
           ((T HAS_SIZE (m + 1) /\
             (!j i:num.
                j IN T /\ i IN T /\ ~(i = j)
                ==> ~(j divides i))) \/
            (T HAS_SIZE (n + 1) /\
             (!j i:num.
                j IN T /\ i IN T /\ j < i
                ==> j divides i)))`;;
