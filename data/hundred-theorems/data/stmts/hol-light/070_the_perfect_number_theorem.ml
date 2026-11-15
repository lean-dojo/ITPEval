(* ========================================================================= *)
(* Perfect number theorems.                                                  *)
(* ========================================================================= *)

needs "Library/prime.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The sum-of-divisors function.                                             *)
(* ------------------------------------------------------------------------- *)

let sigma = new_definition
 `sigma(n) = if n = 0 then 0 else nsum {d | d divides n} (\i. i)`;;

(* ------------------------------------------------------------------------- *)
(* Definition of perfection.                                                 *)
(* ------------------------------------------------------------------------- *)

let perfect = new_definition
 `perfect n <=> ~(n = 0) /\ sigma(n) = 2 * n`;;

(* ------------------------------------------------------------------------- *)
(* Various number-theoretic lemmas.                                          *)
(* ------------------------------------------------------------------------- *)

let ODD_POW2_MINUS1 = `!k. ~(k = 0) ==> ODD(2 EXP k - 1)`;;

let EVEN_ODD_DECOMP = `!n. ~(n = 0) ==> ?r s. ODD s /\ n = 2 EXP r * s`;;

let FINITE_DIVISORS = `!n. ~(n = 0) ==> FINITE {d | d divides n}`;;

let MULT_EQ_COPRIME = `!a b x y. a * b = x * y /\ coprime(a,x)
             ==> ?d. y = a * d /\ b = x * d`;;

let COPRIME_ODD_POW2 = `!k n. ODD(n) ==> coprime(2 EXP k,n)`;;

let MULT_NSUM = `!s t. FINITE s /\ FINITE t
         ==> nsum s f * nsum t g =
             nsum {(x:A,y:B) | x IN s /\ y IN t} (\(x,y). f(x) * g(y))`;;

(* ------------------------------------------------------------------------- *)
(* Some elementary properties of the sigma function.                         *)
(* ------------------------------------------------------------------------- *)

let SIGMA_0 = `sigma 0 = 0`;;

let SIGMA_1 = `sigma(1) = 1`;;

let SIGMA_LBOUND = `!n. 1 < n ==> n + 1 <= sigma(n)`;;

let SIGMA_MULT = `!a b. 1 < a /\ 1 < b ==> 1 + b + a * b <= sigma(a * b)`;;

let SIGMA_PRIME = `!p. prime(p) ==> sigma(p) = p + 1`;;

let SIGMA_PRIME_EQ = `!p. prime(p) <=> sigma(p) = p + 1`;;

let SIGMA_POW2 = `!k. sigma(2 EXP k) = 2 EXP (k + 1) - 1`;;

(* ------------------------------------------------------------------------- *)
(* Multiplicativity of sigma, the most interesting property.                 *)
(* ------------------------------------------------------------------------- *)

let SIGMA_MULTIPLICATIVE = `!a b. coprime(a,b) ==> sigma(a * b) = sigma(a) * sigma(b)`;;

(* ------------------------------------------------------------------------- *)
(* Hence the main theorems.                                                  *)
(* ------------------------------------------------------------------------- *)

let PERFECT_EUCLID = `!k. prime(2 EXP k - 1) ==> perfect(2 EXP (k - 1) * (2 EXP k - 1))`;;

let PERFECT_EULER = `!n. EVEN(n) /\ perfect(n)
       ==> ?k. prime(2 EXP k - 1) /\ n = 2 EXP (k - 1) * (2 EXP k - 1)`;;
