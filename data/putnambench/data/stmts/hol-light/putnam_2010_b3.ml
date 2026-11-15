(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b3:
  classification of the positive integers for which every distribution of
  2010n balls among 2010 labeled boxes can be made uniform by legal box-index
  transfers. This file contains no proof.
*)

let statement =
  `let boxes = 1..2010 in
   let legal_run =
     \(P:num->num->num) (steps:num).
       !t:num.
         t < steps
         ==> ?i j:num.
               i IN boxes /\
               j IN boxes /\
               ~(i = j) /\
               i <= P t i /\
               P (t + 1) i = P t i - i /\
               P (t + 1) j = P t j + i /\
               (!k:num.
                  k IN boxes /\ ~(k = i) /\ ~(k = j)
                  ==> P (t + 1) k = P t k) in
   let solvable =
     \n:num.
       !B:num->num.
         nsum boxes B = 2010 * n
         ==> ?P:num->num->num. ?steps:num.
               (!i:num. i IN boxes ==> P 0 i = B i) /\
               legal_run P steps /\
               (!i:num. i IN boxes ==> P steps i = n) in
   let putnam_2010_b3_solution =
     {n:num | 1005 <= n} in
   !n:num.
     0 < n
     ==> (solvable n <=> n IN putnam_2010_b3_solution)`;;
