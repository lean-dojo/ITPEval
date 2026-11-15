(*
  Statement-only formalization of miniF2F valid problem
  numbertheory_aneqprodakp4_anmsqrtanp1eq2: a real sequence defined by an
  initial value and a finite-product recurrence satisfies a square-root
  identity at positive indices. This file contains no proof.
*)

let statement =
  `!a:num->real.
     (a 0 = &1 /\
      (!n:num. a (n + 1) = product (0..n) a + &4))
     ==> (!n:num. 1 <= n ==> a n - sqrt (a (n + 1)) = &2)`;;
