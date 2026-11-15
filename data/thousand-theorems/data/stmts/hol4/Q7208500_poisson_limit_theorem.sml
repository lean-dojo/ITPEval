(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q7208500 (thousand-theorems__hol4__Q7208500), "Poisson limit theorem":
  for a fixed natural number k and any real sequence p such that n * p n
  converges to r, the corresponding binomial term converges to
  exp (-r) * r^k / k!. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory realTheory transcTheory;
open topologyTheory real_topologyTheory;

val poisson_limit_theorem =
  ``!k : num. !p : num -> real. !r : real.
      (((\n : num. (&n : real) * p n) --> (r : real)) sequentially)
      ==>
      (((\n : num.
          (&(binomial n k) : real) * (p n) pow k *
          (1 - p n) pow (n - k)) -->
        (exp (-r) * (r pow k) / (&(FACT k) : real)))
       sequentially)``;
