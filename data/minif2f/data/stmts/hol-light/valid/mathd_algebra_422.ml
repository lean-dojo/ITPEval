(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_422. This file contains no
  proof.
*)

(*
  miniF2F valid artifact mathd_algebra_422: for the real bijection
  sigma(t) = 5*t - 12 with inverse sigma_inv, the equation
  sigma(x + 1) = sigma_inv(x) forces x = 47/24. This is a statement-only
  formalization and contains no proof.
*)

let statement =
  `!x:real. !sigma sigma_inv:real->real.
     (!t:real. sigma t = &5 * t - &12) /\
     (!t:real. sigma_inv (sigma t) = t) /\
     (!t:real. sigma (sigma_inv t) = t) /\
     sigma (x + &1) = sigma_inv x
     ==> x = &47 / &24`;;
