(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_10,
  catalog title "findExponents": an executable natural-number computation
  removes listed prime factors and returns each listed prime with its exponent,
  under the factorization precondition and postcondition. This file contains
  no proof.
*)

needs "Library/prime.ml";;

let removePrimeFactor = define
  `removePrimeFactor(n,p) =
     if 1 < p /\ 0 < n then
       if n MOD p = 0
       then removePrimeFactor(n DIV p,p)
       else n
     else n`;;

let removeAllPrimeFactors =
  new_recursive_definition list_RECURSION
    `(removeAllPrimeFactors n [] = n) /\
     (!p:num. !ps:num list. !n:num.
        removeAllPrimeFactors n (CONS p ps) =
        removeAllPrimeFactors (removePrimeFactor(n,p)) ps)`;;

let findExponents_precond = new_definition
  `findExponents_precond (n:num) (primes:num list) <=>
     0 < n /\
     0 < LENGTH primes /\
     ALL (\p:num. prime p) primes /\
     PAIRWISE (\p q:num. ~(p = q)) primes /\
     removeAllPrimeFactors n primes = 1`;;

let countFactor = define
  `countFactor(n,p,count) =
     if n = 0 then (count,0)
     else if 0 < n /\ 1 < p then
       if n MOD p = 0
       then countFactor(n DIV p,p,count + 1)
       else (count,n)
     else (count,n)`;;

let countFactors =
  new_recursive_definition list_RECURSION
    `(countFactors n [] = []) /\
     (!p:num. !ps:num list. !n:num.
        countFactors n (CONS p ps) =
        let counted = countFactor(n,p,0) in
        CONS (p,FST counted) (countFactors (SND counted) ps))`;;

let findExponents = new_definition
  `findExponents (n:num) (primes:num list) = countFactors n primes`;;

let factorProduct =
  new_recursive_definition list_RECURSION
    `(factorProduct acc [] = acc) /\
     (!pe:num#num. !rest:(num#num)list. !acc:num.
        factorProduct acc (CONS pe rest) =
        factorProduct (acc * FST pe EXP SND pe) rest)`;;

let findExponents_postcond = new_definition
  `findExponents_postcond
      (n:num) (primes:num list) (result:(num#num)list) <=>
     n = factorProduct 1 result /\
     ALL (\pe:num#num. MEM (FST pe) primes) result /\
     ALL (\p:num. ?pe:num#num. MEM pe result /\ FST pe = p) primes`;;

let findExponents_spec_satisfied =
  `!n:num. !primes:num list.
     findExponents_precond n primes
     ==> findExponents_postcond n primes (findExponents n primes)`;;
