(*
  Statement-only formalization of Thousand Theorems corpus artifact Q472883,
  "Quadratic reciprocity theorem": the Legendre-symbol product formula for
  distinct odd primes and its Jacobi-symbol form for odd natural numbers.
  This file contains no proof.
*)

needs "Library/jacobi.ml";;

let q472883_legendre = new_definition
  `(q472883_legendre:num#num->int)(p,a) = jacobi(a,p)`;;

let Q472883_QUADRATIC_RECIPROCITY_THEOREM =
  `(!p q:num.
      prime p /\
      prime q /\
      ~(p = 2) /\
      ~(q = 2) /\
      ~(p = q)
      ==> q472883_legendre(q,p) * q472883_legendre(p,q) =
          --(&1) pow (p DIV 2 * (q DIV 2))) /\
   (!a b:num.
      ODD a /\
      ODD b
      ==> jacobi(a,b) =
          --(&1) pow (a DIV 2 * (b DIV 2)) * jacobi(b,a))`;;
