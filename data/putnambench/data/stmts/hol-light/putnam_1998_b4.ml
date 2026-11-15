(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_b4:
  the alternating floor-quotient sum for positive integers m and n vanishes
  exactly when their 2-adic valuations differ. This file contains no proof.
*)

let statement =
  `let exact_power_of_two =
     \n k:num.
       2 EXP k divides n /\ ~(2 EXP (k + 1) divides n) in
   let putnam_1998_b4_solution =
     \m n:num.
       ?r s:num.
         exact_power_of_two m r /\
         exact_power_of_two n s /\
         ~(r = s) in
   !m n:num.
     0 < m /\ 0 < n
     ==>
     (isum (0..m * n - 1)
        (\i:num. (--(&1):int) pow (i DIV m + i DIV n)) = &0
      <=> putnam_1998_b4_solution m n)`;;
