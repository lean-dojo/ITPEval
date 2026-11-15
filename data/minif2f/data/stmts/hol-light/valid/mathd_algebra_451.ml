(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_451. This file contains no
  proof.
*)

(*
  miniF2F valid artifact mathd_algebra_451: a real bijection whose inverse
  maps -15 to 0, 0 to 3, 3 to 9, and 9 to 20 satisfies
  sigma(sigma(9)) = 0. This is a statement-only formalization and contains
  no proof.
*)

let statement =
  `!sigma sigma_inv:real->real.
    (!x:real. sigma (sigma_inv x) = x) /\
    (!x:real. sigma_inv (sigma x) = x) /\
    sigma_inv (-- &15) = &0 /\
    sigma_inv (&0) = &3 /\
    sigma_inv (&3) = &9 /\
    sigma_inv (&9) = &20
    ==> sigma (sigma (&9)) = &0`;;
