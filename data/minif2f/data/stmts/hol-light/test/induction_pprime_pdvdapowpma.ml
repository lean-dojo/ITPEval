(*
  Statement-only formalization of miniF2F test problem induction_pprime_pdvdapowpma. This file
  contains no proof.
*)

let statement = `!p a:num.
  0 < a /\ prime p
  ==> p divides (a EXP p - a)`;;
