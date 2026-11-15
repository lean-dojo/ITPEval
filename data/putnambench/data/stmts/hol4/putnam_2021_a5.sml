(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_a5:
  the exponents for which the sum of their powers over the positive residues
  at most 2021 coprime to 2021 is divisible by 2021. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory gcdTheory pred_setTheory;

val putnam_2021_a5 =
  ``!j : num.
      let A =
        {n : num | 1 <= n /\ n <= 2021 /\ gcd n 2021 = 1}
      in
        (divides 2021 (SIGMA (\n : num. n EXP j) A) <=>
         ~divides 42 j /\ ~divides 46 j)``;
