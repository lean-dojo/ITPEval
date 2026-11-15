(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b3:
  the sharp supremum 1/k! of the normalized k-th elementary symmetric sum
  over all finite tuples of positive real numbers. This file contains no proof.
*)

let statement =
  `let esymm =
     \k n (a:num->real).
       sum {s:num->bool | s SUBSET (0..n-1) /\ CARD s = k}
           (\s. product s (\i. a i)) in
   let ratio =
     \k n (a:num->real).
       esymm k n a / (esymm 1 n a) pow k in
   let putnam_1975_b3_solution =
     \k:num. &1 / &(FACT k) in
   !k:num.
     0 < k
     ==>
     ((!n:num. !a:num->real.
         k <= n /\ (!i:num. i < n ==> &0 < a i)
         ==> ratio k n a <= putnam_1975_b3_solution k) /\
      (!M:real.
         M < putnam_1975_b3_solution k
         ==> ?n:num. ?a:num->real.
               k <= n /\
               (!i:num. i < n ==> &0 < a i) /\
               M < ratio k n a))`;;
