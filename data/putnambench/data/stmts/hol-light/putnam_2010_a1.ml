(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a1:
  the largest number of boxes into which 1 through n can be partitioned with
  equal box sums is the ceiling of n divided by 2. This file contains no proof.
*)

let statement =
  `let putnam_2010_a1_solution =
     \n:num. (n + 1) DIV 2 in
   let feasible =
     \n k:num.
       ?boxes:num->num.
         (!m:num.
            m IN (1..n)
            ==> boxes m IN (1..k)) /\
         (!i j:num.
            i IN (1..k) /\ j IN (1..k)
            ==>
            nsum (1..n)
              (\x:num. if boxes x = i then x else 0) =
            nsum (1..n)
              (\x:num. if boxes x = j then x else 0)) in
   !n:num. !kboxes:num->bool.
     0 < n /\
     (!k:num. kboxes k <=> feasible n k)
     ==>
     kboxes (putnam_2010_a1_solution n) /\
     (!k:num.
        kboxes k
        ==> k <= putnam_2010_a1_solution n)`;;
