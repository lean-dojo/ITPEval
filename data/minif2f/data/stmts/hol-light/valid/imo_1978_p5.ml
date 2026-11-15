(*
  Statement-only formalization of miniF2F valid problem imo_1978_p5. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1978_p5: an injective sequence of natural
  numbers fixing zero satisfies the stated finite harmonic-sum inequality.
  This is a statement-only formalization and contains no proof.
*)

let imo_1978_p5 =
  `!n:num a:num->num.
     (!x y. a x = a y ==> x = y) /\
     a 0 = 0 /\
     0 < n
     ==> sum (1..n) (\k:num. &1 / &k) <=
         sum (1..n) (\k:num. &(a k) / (&k pow 2))`;;
