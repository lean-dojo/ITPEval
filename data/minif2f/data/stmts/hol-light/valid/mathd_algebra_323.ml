(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_323. This file contains no
  proof.
*)

(*
  miniF2F valid problem mathd_algebra_323: for the real bijection
  sigma(x) = x^3 - 8, sigma^{-1}(sigma(sigma^{-1}(19))) = 3.
  This is a statement-only formalization and contains no proof.
*)

let statement =
  `!sigma sigma_inv:real->real.
     (!x:real. sigma x = x pow 3 - &8) /\
     (!x:real. sigma_inv (sigma x) = x) /\
     (!x:real. sigma (sigma_inv x) = x)
     ==> sigma_inv (sigma (sigma_inv (&19))) = &3`;;
