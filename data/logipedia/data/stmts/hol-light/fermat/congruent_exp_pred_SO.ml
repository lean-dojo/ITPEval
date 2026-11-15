(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.congruent_exp_pred_SO, catalog title
  "fermat.congruent_exp_pred_SO": Fermat's little theorem in congruence form
  for a natural prime not dividing the base. This file contains no proof.
*)

let statement =
  `!p a:num.
     prime p
     ==> ~(p divides a)
     ==> (a EXP (p - 1)) MOD p = 1 MOD p`;;
