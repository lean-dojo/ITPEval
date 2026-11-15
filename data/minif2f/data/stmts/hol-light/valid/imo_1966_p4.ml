(*
  Statement-only formalization of miniF2F valid artifact imo_1966_p4: the
  finite sum of reciprocal sines at dyadically scaled angles equals a
  difference of reciprocal tangents away from dyadic half-period points.
  This file contains no proof.
*)

needs "Library/transc.ml";;

let imo_1966_p4 =
  `!n:num x:real.
     (!k:num. 0 < k ==> !m:int.
        ~(x = real_of_int m * pi / ((&2:real) pow k))) /\
     0 < n
     ==> sum (1..n) (\k:num. &1 / sin (((&2:real) pow k) * x)) =
         &1 / tan x - &1 / tan (((&2:real) pow n) * x)`;;
