(* ========================================================================= *)
(* Liouville approximation theorem.                                          *)
(* ========================================================================= *)

needs "Library/floor.ml";;
needs "Library/poly.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of algebraic and transcendental.                               *)
(* ------------------------------------------------------------------------- *)

let algebraic = new_definition
 `algebraic(x) <=> ?p. ALL integer p /\ ~(poly p = poly []) /\ poly p x = &0`;;

let transcendental = new_definition
 `transcendental(x) <=> ~(algebraic x)`;;

(* ------------------------------------------------------------------------- *)
(* Some trivialities.                                                        *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGER_EQ_0 = `!x. integer x /\ abs(x) < &1 ==> x = &0`;;

let FACT_LE_REFL = `!n. n <= FACT n`;;

let EXP_LE_REFL = `!a. 1 < a ==> !n. n <= a EXP n`;;

(* ------------------------------------------------------------------------- *)
(* Inequality variant of mean value theorem.                                 *)
(* ------------------------------------------------------------------------- *)

let MVT_INEQ = `!f f' a d M.
        &0 < M /\ &0 < d /\
        (!x. abs(x - a) <= d ==> (f diffl f'(x)) x /\ abs(f' x) < M)
        ==> !x. abs(x - a) <= d ==> abs(f x - f a) < M * d`;;

(* ------------------------------------------------------------------------- *)
(* Appropriate multiple of poly on rational is an integer.                   *)
(* ------------------------------------------------------------------------- *)

let POLY_MULTIPLE_INTEGER = `!p q l. ALL integer l ==> integer(&q pow (LENGTH l) * poly l (&p / &q))`;;

(* ------------------------------------------------------------------------- *)
(* First show any root is surrounded by an other-root-free zone.             *)
(* ------------------------------------------------------------------------- *)

let SEPARATE_FINITE_SET = `!a s. FINITE s
         ==> ~(a IN s) ==> ?d. &0 < d /\ !x. x IN s ==> d <= abs(x - a)`;;

let POLY_ROOT_SEPARATE_LE = `!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?d. &0 < d /\
                 !x'. &0 < abs(x' - x) /\ abs(x' - x) < d
                      ==> ~(poly p x' = &0)`;;

let POLY_ROOT_SEPARATE_LT = `!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?d. &0 < d /\
                 !x'. &0 < abs(x' - x) /\ abs(x' - x) <= d
                      ==> ~(poly p x' = &0)`;;

(* ------------------------------------------------------------------------- *)
(* And also there is a positive bound on a polynomial in an interval.        *)
(* ------------------------------------------------------------------------- *)

let POLY_BOUND_INTERVAL = `!p d x. ?M. &0 < M /\ !x'. abs(x' - x) <= d ==> abs(poly p x') < M`;;

(* ------------------------------------------------------------------------- *)
(* Now put these together to get the interval we need.                       *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_INTERVAL = `!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?c. &0 < c /\
                 (!x'. abs(x' - x) <= c
                       ==> abs(poly(poly_diff p) x') < &1 / c) /\
                 (!x'. &0 < abs(x' - x) /\ abs(x' - x) <= c
                       ==> ~(poly p x' = &0))`;;

(* ------------------------------------------------------------------------- *)
(* Liouville's approximation theorem.                                        *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE = `!x. algebraic x
       ==> ?n c. c > &0 /\
                 !p q. ~(q = 0) ==> &p / &q = x \/
                                    abs(x - &p / &q) > c / &q pow n`;;

(* ------------------------------------------------------------------------- *)
(* Corollary for algebraic irrationals.                                      *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_IRRATIONAL = `!x. algebraic x /\ ~rational x
       ==> ?n c. c > &0 /\ !p q. ~(q = 0) ==> abs(x - &p / &q) > c / &q pow n`;;

(* ------------------------------------------------------------------------- *)
(* Liouville's constant.                                                     *)
(* ------------------------------------------------------------------------- *)

let liouville = new_definition
 `liouville = suminf (\n. &1 / &10 pow (FACT n))`;;

(* ------------------------------------------------------------------------- *)
(* Some bounds on the partial sums and hence convergence.                    *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_SUM_BOUND = `!d n. ~(n = 0)
         ==> sum(n..n+d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`;;

let LIOUVILLE_PSUM_BOUND = `!n d. ~(n = 0)
         ==> sum(n,d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`;;

let LIOUVILLE_SUMS = `(\k. &1 / &10 pow FACT k) sums liouville`;;

let LIOUVILLE_PSUM_LE = `!n. sum(0,n) (\k. &1 / &10 pow FACT k) <= liouville`;;

let LIOUVILLE_PSUM_LT = `!n. sum(0,n) (\k. &1 / &10 pow FACT k) < liouville`;;

let LIOVILLE_PSUM_DIFF = `!n. ~(n = 0)
       ==> liouville
             <= sum(0,n) (\k. &1 / &10 pow FACT k) + &2 / &10 pow (FACT n)`;;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let TRANSCENDENTAL_LIOUVILLE = `transcendental(liouville)`;;
