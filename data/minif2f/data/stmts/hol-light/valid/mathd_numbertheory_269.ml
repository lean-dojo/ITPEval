(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_269:
  the remainder modulo 100 of 2005^2 + 2005^0 + 2005^0 + 2005^5 is 52.
  This file contains no proof.
*)

let statement =
  `(2005 EXP 2 + 2005 EXP 0 + 2005 EXP 0 + 2005 EXP 5) MOD 100 = 52`;;
