(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q132469, "Fermat's Last Theorem": for every natural exponent at least
  three, no three nonzero natural numbers satisfy a^n + b^n = c^n. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val FermatLastTheorem =
  ``!n : num.
      3 <= n ==>
      !a b c : num.
        a <> 0 ==>
        b <> 0 ==>
        c <> 0 ==>
        a EXP n + b EXP n <> c EXP n``;
