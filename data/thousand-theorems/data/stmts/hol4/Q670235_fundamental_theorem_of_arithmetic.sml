(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q670235, "Fundamental theorem of arithmetic": every list of prime natural
  numbers with product n has the canonical multiset of prime factors of n,
  equivalently uniquely determines the factorization up to permutation. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory bagTheory containerTheory listTheory primeFactorTheory;

val primeFactorsList_unique =
  ``!(n : num) (l : num list).
      FOLDL (\acc p : num. acc * p) 1 l = n /\
      EVERY prime l
      ==>
      LIST_TO_BAG l = PRIME_FACTORS n``;
