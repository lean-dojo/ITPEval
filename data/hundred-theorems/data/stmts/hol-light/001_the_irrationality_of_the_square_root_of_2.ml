(* ========================================================================= *)
(* Irrationality of sqrt(2) and more general results.                        *)
(* ========================================================================= *)

needs "Library/prime.ml";;              (* For number-theoretic lemmas       *)
needs "Library/floor.ml";;              (* For definition of rationals       *)

(* ------------------------------------------------------------------------- *)
(* Most general irrationality of square root result.                         *)
(* ------------------------------------------------------------------------- *)

let IRRATIONAL_SQRT_NONSQUARE = `!n. rational(sqrt(&n)) ==> ?m. n = m EXP 2`;;

(* ------------------------------------------------------------------------- *)
(* In particular, prime numbers.                                             *)
(* ------------------------------------------------------------------------- *)

let IRRATIONAL_SQRT_PRIME = `!p. prime p ==> ~rational(sqrt(&p))`;;

(* ------------------------------------------------------------------------- *)
(* In particular, sqrt(2) is irrational.                                     *)
(* ------------------------------------------------------------------------- *)

let IRRATIONAL_SQRT_2 = `~rational(sqrt(&2))`;;
