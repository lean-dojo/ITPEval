(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_a6:
  equality of the sums of squared coefficients of every positive power of
  two specified real quadratic polynomials. This file contains no proof.
*)

needs "Library/iter.ml";;

let statement =
  `let pmul =
     \p q:num->real. \k:num.
       sum (0..k) (\i:num. p i * q (k - i)) in
   let ppow =
     \p:num->real. \n:num.
       ITER n (pmul p) (\k:num. if k = 0 then &1 else &0) in
   let gamma =
     \p:num->real.
       sum {k:num | ~(p k = &0)} (\k:num. (p k) pow 2) in
   let f =
     \k:num.
       if k = 0 then &2
       else if k = 1 then &7
       else if k = 2 then &3
       else &0 in
   let g =
     \k:num.
       if k = 0 then &1
       else if k = 1 then &5
       else if k = 2 then &6
       else &0 in
   g 0 = &1 /\
   (!n:num.
      1 <= n
      ==> gamma (ppow f n) = gamma (ppow g n))`;;
