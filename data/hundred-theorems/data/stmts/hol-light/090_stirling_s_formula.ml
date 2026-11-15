(* ========================================================================= *)
(* Stirling's approximation.                                                 *)
(* ========================================================================= *)

needs "Library/analysis.ml";;
needs "Library/transc.ml";;

override_interface("-->",`(tends_num_real)`);;

(* ------------------------------------------------------------------------- *)
(* This is a handy induction for Wallis's product below.                     *)
(* ------------------------------------------------------------------------- *)

let ODDEVEN_INDUCT = `!P. P 0 /\ P 1 /\ (!n. P n ==> P(n + 2)) ==> !n. P n`;;

(* ------------------------------------------------------------------------- *)
(* A particular limit we need below.                                         *)
(* ------------------------------------------------------------------------- *)

let LN_LIM_BOUND = `!n. ~(n = 0) ==> abs(&n * ln(&1 + &1 / &n) - &1) <= &1 / (&2 * &n)`;;

let LN_LIM_LEMMA = `(\n. &n * ln(&1 + &1 / &n)) --> &1`;;

(* ------------------------------------------------------------------------- *)
(* Lemma for proving inequality via derivative and limit at infinity.        *)
(* ------------------------------------------------------------------------- *)

let POSITIVE_DIFF_LEMMA = `!f f'. (!x. &0 < x ==> (f diffl f'(x)) x /\ f'(x) < &0) /\
          (\n. f(&n)) --> &0
          ==> !n. ~(n = 0) ==> &0 < f(&n)`;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary definition.                                                     *)
(* ------------------------------------------------------------------------- *)

let stirling = new_definition
 `stirling n = ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n)`;;

(* ------------------------------------------------------------------------- *)
(* This difference is a decreasing sequence.                                 *)
(* ------------------------------------------------------------------------- *)

let STIRLING_DIFF = `!n. ~(n = 0)
       ==> stirling(n) - stirling(n + 1) =
           (&n + &1 / &2) * ln((&n + &1) / &n) - &1`;;

let STIRLING_DELTA_DERIV = `!x. &0 < x
       ==> ((\x. ln ((x + &1) / x) - &1 / (x + &1 / &2)) diffl
            (-- &1 / (x * (x + &1) * (&2 * x + &1) pow 2))) x`;;

let STIRLING_DELTA_LIMIT = `(\n. ln ((&n + &1) / &n) - &1 / (&n + &1 / &2)) --> &0`;;

let STIRLING_DECREASES = `!n. ~(n = 0) ==> stirling(n + 1) < stirling(n)`;;

(* ------------------------------------------------------------------------- *)
(* However a slight tweak gives an *increasing* sequence.                    *)
(* ------------------------------------------------------------------------- *)

let OTHER_DERIV_LEMMA = `!x. &0 < x
       ==> ((\x. &1 / (&12 * x * (x + &1) * (x + &1 / &2))) diffl
            --(&3 * x pow 2 + &3 * x + &1 / &2) /
              (&12 * (x * (x + &1) * (x + &1 / &2)) pow 2)) x`;;

let STIRLING_INCREASES = `!n. ~(n = 0)
       ==> stirling(n + 1) - &1 / (&12 * (&(n + 1)))
           > stirling(n) - &1 / (&12 * &n)`;;

(* ------------------------------------------------------------------------- *)
(* Hence it converges to *something*.                                        *)
(* ------------------------------------------------------------------------- *)

let STIRLING_UPPERBOUND = `!n. stirling(SUC n) <= &1`;;

let STIRLING_LOWERBOUND = `!n. -- &1 <= stirling(SUC n)`;;

let STIRLING_MONO = `!m n. ~(m = 0) /\ m <= n ==> stirling n <= stirling m`;;

let STIRLING_CONVERGES = `?c. stirling --> c`;;

(* ------------------------------------------------------------------------- *)
(* Now derive Wallis's infinite product.                                     *)
(* ------------------------------------------------------------------------- *)

let [PI2_LT; PI2_LE; PI2_NZ] = (CONJUNCTS o prove)
 (`&0 < pi / &2 /\ &0 <= pi / &2 /\ ~(pi / &2 = &0)`,
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let WALLIS_PARTS = `!n. (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) * integral(&0,pi / &2) (\x. sin(x) pow n)`;;

let WALLIS_PARTS' = `!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) / (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow n)`;;

let WALLIS_0 = `integral(&0,pi / &2) (\x. sin(x) pow 0) = pi / &2`;;

let WALLIS_1 = `integral(&0,pi / &2) (\x. sin(x) pow 1) = &1`;;

let WALLIS_EVEN = `!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) =
         (&(FACT(2 * n)) / (&2 pow n * &(FACT n)) pow 2) * pi / &2`;;

let WALLIS_ODD = `!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
         (&2 pow n * &(FACT n)) pow 2 / &(FACT(2 * n + 1))`;;

let WALLIS_QUOTIENT = `!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
        (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4 *
        pi / &2`;;

let WALLIS_QUOTIENT' = `!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) * &2 / pi =
         (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4`;;

let WALLIS_MONO = `!m n. m <= n
         ==> integral(&0,pi / &2) (\x. sin(x) pow n)
                <= integral(&0,pi / &2) (\x. sin(x) pow m)`;;

let WALLIS_LT = `!n. &0 < integral(&0,pi / &2) (\x. sin(x) pow n)`;;

let WALLIS_NZ = `!n. ~(integral(&0,pi / &2) (\x. sin(x) pow n) = &0)`;;

let WALLIS_BOUNDS = `!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 1))
        <= integral(&0,pi / &2) (\x. sin(x) pow n) /\
       integral(&0,pi / &2) (\x. sin(x) pow n) <=
        (&n + &2) / (&n + &1) * integral(&0,pi / &2) (\x. sin(x) pow (n + 1))`;;

let WALLIS_RATIO_BOUNDS = `!n. &1 <= integral(&0,pi / &2) (\x. sin(x) pow n) /
            integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) /\
      integral(&0,pi / &2) (\x. sin(x) pow n) /
      integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) <= (&n + &2) / (&n + &1)`;;

let WALLIS = `(\n. (&2 pow n * &(FACT n)) pow 4 / (&(FACT(2 * n)) * &(FACT(2 * n + 1))))
   --> pi / &2`;;

(* ------------------------------------------------------------------------- *)
(* Hence determine the actual value of the limit.                            *)
(* ------------------------------------------------------------------------- *)

let LN_WALLIS = `(\n. &4 * &n * ln(&2) + &4 * ln(&(FACT n)) -
        (ln(&(FACT(2 * n))) + ln(&(FACT(2 * n + 1))))) --> ln(pi / &2)`;;

let STIRLING = `(\n. ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n + ln(&2 * pi) / &2))
   --> &0`;;
