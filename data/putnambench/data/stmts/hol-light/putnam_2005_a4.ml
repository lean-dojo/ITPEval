(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_a4:
  an all-ones submatrix of a real sign matrix with mutually orthogonal rows
  has the product of its dimensions at most the matrix order. This file
  contains no proof.
*)

let statement =
  `!n a b:num. !H:N->N->real. !S:A->B->real.
     1 <= n /\
     (:N) HAS_SIZE n /\
     (!i j:N. H i j = &1 \/ H i j = -- &1) /\
     (!i j:N.
        ~(i = j)
        ==> sum (:N) (\k:N. H i k * H j k) = &0) /\
     1 <= a /\ a <= n /\ 1 <= b /\ b <= n /\
     (:A) HAS_SIZE a /\
     (:B) HAS_SIZE b /\
     (?rri:A->N. ?cri:B->N.
        (!i j:A. rri i = rri j ==> i = j) /\
        (!i j:B. cri i = cri j ==> i = j) /\
        (!i:A. !j:B. S i j = H (rri i) (cri j))) /\
     (!i:A. !j:B. S i j = &1)
     ==> a * b <= n`;;
