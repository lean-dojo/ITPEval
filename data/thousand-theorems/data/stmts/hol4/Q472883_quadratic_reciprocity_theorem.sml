(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q472883, "Quadratic reciprocity theorem": the reciprocity laws for Legendre
  symbols of distinct odd primes and for Jacobi symbols of arbitrary odd
  natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory bagTheory dividesTheory integerTheory primeFactorTheory;

val q472883_legendre_sym_def = Define`
  q472883_legendre_sym (p : num) (a : num) =
    if a MOD p = 0 then (0 : int)
    else if ?x : num. (x EXP 2) MOD p = a MOD p then 1
    else -1`;

val q472883_jacobi_sym_def = Define`
  q472883_jacobi_sym (a : num) (b : num) =
    if b = 0 then (1 : int)
    else
      ITBAG
        (\p acc. q472883_legendre_sym p a * acc)
        (PRIME_FACTORS b)
        1`;

val q472883_legendre_quadratic_reciprocity =
  ``!(p : num) (q : num).
      prime p /\
      prime q /\
      ~(p = 2) /\
      ~(q = 2) /\
      ~(p = q)
      ==>
      q472883_legendre_sym q p * q472883_legendre_sym p q =
      if EVEN ((p DIV 2) * (q DIV 2))
      then (1 : int)
      else -1``;

val q472883_jacobi_quadratic_reciprocity =
  ``!(a : num) (b : num).
      ODD a /\ ODD b
      ==>
      q472883_jacobi_sym a b =
      (if EVEN ((a DIV 2) * (b DIV 2))
       then (1 : int)
       else -1) *
      q472883_jacobi_sym b a``;
