(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b4:
  symmetry in the number of integer tuples of a given positive length whose
  sum of absolute values has a given positive bound. This file contains no
  proof.
*)

let statement =
  `!m n:int. !f:int->int->num.
     &0 < m /\
     &0 < n /\
     (!m' n':int.
        &0 < m' /\ &0 < n'
        ==>
        f m' n' =
        CARD
          {x:int list |
             &(LENGTH x) = n' /\
             isum {i:num | i < LENGTH x} (\i. abs (EL i x)) <= m'})
     ==>
     f m n = f n m`;;
