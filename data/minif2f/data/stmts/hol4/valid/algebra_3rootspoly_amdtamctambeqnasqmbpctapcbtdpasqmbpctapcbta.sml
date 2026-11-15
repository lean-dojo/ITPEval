(*
  Statement-only formalization of miniF2F valid problem
  algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta: a polynomial
  factorization identity in four complex variables. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta =
  ``!b c d a : complex.
      (a - d) * (a - c) * (a - b) =
        -(((a pow 2 - (b + c) * a) + c * b) * d) +
        ((a pow 2 - (b + c) * a) + c * b) * a``;
