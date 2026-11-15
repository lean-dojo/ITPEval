(*
  Statement-only formalization of miniF2F test problem mathd_algebra_188. This file contains no
  proof.
*)

let statement =
  `!sigma inv_sigma:real->real.
     (!x:real.
        sigma (inv_sigma x) = x /\
        inv_sigma (sigma x) = x) /\
     sigma (&2) = inv_sigma (&2)
     ==> sigma (sigma (&2)) = &2`;;
