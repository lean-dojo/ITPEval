(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b6
  (putnambench__hol-light__putnam_2018_b6): an upper bound on the number of
  length-2018 sequences over {1,2,3,4,5,6,10} with sum 3860. This file
  contains no proof.
*)

let statement =
  `let S =
     {s:num list |
        LENGTH s = 2018 /\
        (!x:num.
           MEM x s
           ==> x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/
               x = 5 \/ x = 6 \/ x = 10) /\
        ITLIST (\x acc. x + acc) s 0 = 3860} in
   &(CARD S) <=
   ((&2:real) pow 3860) * ((&2018 / &2048) pow 2018)`;;
