(*
  Statement-only formalization of Logipedia corpus artifact
  cong.transitive_congruent, catalog title "cong.transitive_congruent":
  congruence of natural numbers modulo any natural modulus is transitive.
  This file contains no proof.
*)

let statement =
  `!p x y z:num.
     x MOD p = y MOD p
     ==> y MOD p = z MOD p
     ==> x MOD p = z MOD p`;;
