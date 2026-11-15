(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_393. This file contains no
  proof.
*)

(*
  miniF2F valid artifact mathd_algebra_393: the inverse of the real bijection
  sigma(x) = 4 * x^3 + 1 maps 33 to 2. This is a statement-only
  formalization and contains no proof.
*)

let statement =
  `!sigma:real->real.
     (!x:real. sigma x = &4 * x pow 3 + &1) /\
     BIJ sigma UNIV UNIV
     ==> ?sigma_inv:real->real.
           (!x:real. sigma_inv (sigma x) = x) /\
           (!y:real. sigma (sigma_inv y) = y) /\
           sigma_inv (&33) = &2`;;
