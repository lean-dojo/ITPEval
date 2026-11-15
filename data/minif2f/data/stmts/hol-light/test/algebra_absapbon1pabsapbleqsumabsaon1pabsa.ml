(*
  Statement-only formalization of miniF2F test problem
  algebra_absapbon1pabsapbleqsumabsaon1pabsa. This file contains no proof.
*)

let algebra_absapbon1pabsapbleqsumabsaon1pabsa =
  `!a b:real.
     abs (a + b) / (&1 + abs (a + b))
     <= abs a / (&1 + abs a) + abs b / (&1 + abs b)`;;
