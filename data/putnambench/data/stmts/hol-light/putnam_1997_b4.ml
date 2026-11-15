(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_b4:
  bounds on an alternating sum of coefficients of powers of 1 + x + x^2.
  This file contains no proof.
*)

needs "Library/iter.ml";;

let statement =
  `let pmul =
     \p q:num->int. \n:num.
       isum (0..n) (\i:num. p i * q (n - i)) in
   let ppow =
     \p:num->int. \m:num.
       ITER m (pmul p) (\n:num. if n = 0 then &1 else &0) in
   let trinomial =
     \n:num. if n <= 2 then &1 else &0 in
   !a:num->num->int.
     (!m n:num. a m n = ppow trinomial m n)
     ==> !k:num.
           &0 <=
           isum (0..((2 * k) DIV 3))
                (\i:num. (-- &1) pow i * a (k - i) i) /\
           isum (0..((2 * k) DIV 3))
                (\i:num. (-- &1) pow i * a (k - i) i)
           <= &1`;;
