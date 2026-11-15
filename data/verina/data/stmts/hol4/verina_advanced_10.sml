(*
  Statement-only formalization of VERINA artifact verina_advanced_10,
  cataloged as "findExponents": the program computes, for each supplied
  prime, its exponent in the factorization of a positive natural number.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory primeTheory;

val removePrimeFactorFuel_def = Define `
  (removePrimeFactorFuel 0 (n : num) (p : num) = n) /\
  (removePrimeFactorFuel (SUC fuel) n p =
     if 1 < p /\ 0 < n then
       if n MOD p = 0 then
         removePrimeFactorFuel fuel (n DIV p) p
       else
         n
     else
       n)
`;

val removePrimeFactor_def = new_definition (
  "removePrimeFactor_def",
  ``removePrimeFactor (n : num) (p : num) =
      removePrimeFactorFuel n n p``
);

val removeAllPrimeFactors_def = new_definition (
  "removeAllPrimeFactors_def",
  ``removeAllPrimeFactors (n : num) (primes : num list) =
      FOLDL removePrimeFactor n primes``
);

val findExponents_precond_def = new_definition (
  "findExponents_precond_def",
  ``findExponents_precond (n : num) (primes : num list) <=>
      0 < n /\
      0 < LENGTH primes /\
      EVERY prime primes /\
      ALL_DISTINCT primes /\
      removeAllPrimeFactors n primes = 1``
);

val countFactorFuel_def = Define `
  (countFactorFuel 0 (n : num) (p : num) (count : num) = (count,n)) /\
  (countFactorFuel (SUC fuel) n p count =
     if n = 0 then
       (count,0)
     else if 0 < n /\ 1 < p then
       if n MOD p = 0 then
         countFactorFuel fuel (n DIV p) p (count + 1)
       else
         (count,n)
     else
       (count,n))
`;

val countFactor_def = new_definition (
  "countFactor_def",
  ``countFactor (n : num) (p : num) (count : num) =
      countFactorFuel n n p count``
);

val countFactors_def = Define `
  (countFactors (n : num) ([] : num list) = ([] : (num # num) list)) /\
  (countFactors n (p::ps) =
     let counted = countFactor n p 0
     in
       (p,FST counted)::countFactors (SND counted) ps)
`;

val findExponents_def = new_definition (
  "findExponents_def",
  ``findExponents (n : num) (primes : num list) =
      countFactors n primes``
);

val findExponents_postcond_def = new_definition (
  "findExponents_postcond_def",
  ``findExponents_postcond
      (n : num) (primes : num list) (result : (num # num) list) <=>
      n = FOLDL (\acc pe. acc * FST pe EXP SND pe) 1 result /\
      EVERY (\pe. MEM (FST pe) primes) result /\
      EVERY (\p. EXISTS (\pe. FST pe = p) result) primes``
);

val findExponents_spec_satisfied =
  ``!(n : num) (primes : num list).
      findExponents_precond n primes ==>
      findExponents_postcond n primes (findExponents n primes)``;
