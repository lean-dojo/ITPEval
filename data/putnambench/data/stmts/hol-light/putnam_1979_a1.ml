(*
  Statement-only formalization of PutnamBench artifact putnam_1979_a1:
  the finite multiset of positive integers with sum 1979 whose product is
  greatest consists of one 2 and 659 copies of 3. This file contains no proof.
*)

let statement =
  `let finite_multiset =
     \m:num->num. FINITE {x:num | ~(m x = 0)} in
   let multiset_sum =
     \m:num->num. nsum {x:num | ~(m x = 0)} (\x. m x * x) in
   let multiset_product =
     \m:num->num. nproduct {x:num | ~(m x = 0)} (\x. x EXP (m x)) in
   let putnam_1979_a1_solution =
     \x:num. if x = 2 then 1 else if x = 3 then 659 else 0 in
   !P:(num->num)->bool.
     (!m:num->num.
        P m <=>
        finite_multiset m /\
        (?x:num. ~(m x = 0)) /\
        (!x:num. ~(m x = 0) ==> x > 0) /\
        multiset_sum m = 1979)
     ==>
     P putnam_1979_a1_solution /\
     (!m:num->num.
        P m
        ==> multiset_product putnam_1979_a1_solution >=
            multiset_product m)`;;
