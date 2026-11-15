(*
  Statement-only formalization of Thousand Theorems corpus artifact Q550402
  (thousand-theorems__hol-light__Q550402), "Dirichlet's theorem on arithmetic
  progressions": for every positive natural modulus and coprime residue class,
  infinitely many primes lie in that class. This file contains no proof.
*)

let Q550402_DIRICHLETS_THEOREM_ON_ARITHMETIC_PROGRESSIONS =
  `!q a:num.
     1 <= q /\ coprime(a,q)
     ==> INFINITE {p | prime p /\ (p == a) (mod q)}`;;
