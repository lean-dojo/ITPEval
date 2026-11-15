(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_31. This file contains no
  proof.
*)

(*
  miniF2F valid artifact mathd_algebra_31: for a nonnegative real parameter
  and nonnegative real sequence, the square-root recurrence and convergence
  to 9 imply that 9 is the corresponding fixed point. This is a
  statement-only formalization and contains no proof.
*)

let statement =
  `!x:real u:num->real.
     &0 <= x /\
     (!n:num. &0 <= u n) /\
     (!n:num. u (n + 1) = sqrt (x + u n)) /\
     (!e:real. &0 < e
               ==> ?N:num. !n:num. N <= n ==> abs (u n - &9) < e)
     ==> &9 = sqrt (x + &9)`;;
