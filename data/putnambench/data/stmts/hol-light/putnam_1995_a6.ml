(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a6:
  for some n at least 1995, matrices whose columns are permutations of
  {1,2,3} have consecutive row sums at least four times as often as equal row
  sums. This file contains no proof.
*)

let statement =
  `let admissible_matrix =
     \n:num. \A:num->num->int.
       (!j:num.
          j < n
          ==> IMAGE (\i:num. A i j) (0..2) =
              {(&1:int),(&2:int),(&3:int)}) /\
       (!i j:num.
          ~(i < 3 /\ j < n)
          ==> A i j = &0) in
   let row_sums =
     \n:num. \A:num->num->int.
       IMAGE
         (\i:num. isum (0..n-1) (\j:num. A i j))
         (0..2) in
   let consecutive =
     \s:int->bool.
       s HAS_SIZE 3 /\
       ?a b c:int.
         {a,b,c} = s /\
         b = a + &1 /\
         c = a + &2 in
   ?n:num.
     1995 <= n /\
     CARD
       {A:num->num->int |
          admissible_matrix n A /\
          consecutive (row_sums n A)}
     >=
     4 *
     CARD
       {A:num->num->int |
          admissible_matrix n A /\
          row_sums n A HAS_SIZE 1}`;;
