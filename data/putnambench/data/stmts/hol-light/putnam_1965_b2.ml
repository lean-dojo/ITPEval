(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b2:
  equality of the sums of squared win and loss counts in a finite
  round-robin tournament. This file contains no proof.
*)

let statement =
  `!n:num. !won:A->A->bool. !w l:A->int.
     1 < n /\
     (:A) HAS_SIZE n /\
     (!i:A. ~won i i) /\
     (!i j:A. ~(i = j) ==> (won i j <=> ~won j i)) /\
     w = (\r:A. isum (:A) (\j. if won r j then (&1:int) else &0)) /\
     l = (\r:A. &n - &1 - w r)
     ==> isum (:A) (\r. (w r) pow 2) =
         isum (:A) (\r. (l r) pow 2)`;;
