(*
  Statement-only formalization of miniF2F valid problem aimeII_2001_p3. This file contains no
  proof.
*)

let statement = `!x:num->int.
    (x 1 = &211) /\
    (x 2 = &375) /\
    (x 3 = &420) /\
    (x 4 = &523) /\
    (!n:num. 5 <= n ==>
      x n = x (n - 1) - x (n - 2) + x (n - 3) - x (n - 4))
    ==> x 531 + x 753 + x 975 = &898`;;
