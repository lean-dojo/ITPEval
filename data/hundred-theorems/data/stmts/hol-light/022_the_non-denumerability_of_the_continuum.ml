(* ========================================================================= *)
(* #22: non-denumerability of continuum (= uncountability of the reals).     *)
(* ========================================================================= *)

needs "Library/card.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Definition of countability.                                               *)
(* ------------------------------------------------------------------------- *)

let countable = new_definition
  `countable s <=> s <=_c (UNIV:num->bool)`;;

(* ------------------------------------------------------------------------- *)
(* Set of repeating digits and its countability.                             *)
(* ------------------------------------------------------------------------- *)

let repeating = new_definition
 `repeating = {s:num->bool | ?n. !m. m >= n ==> s m}`;;

let BINARY_BOUND = `!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) < 2 EXP (n + 1)`;;

let BINARY_DIV_POW2 = `!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0)) DIV (2 EXP (SUC n)) = 0`;;

let PLUS_MOD_REFL = `!a b. ~(b = 0) ==> (a + b) MOD b = a MOD b`;;

let BINARY_PLUS_DIV_POW2 = `!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0) + 2 EXP (SUC n))
       DIV (2 EXP (SUC n)) = 1`;;

let BINARY_UNIQUE_LEMMA = `!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) =
       nsum(0..n) (\i. if c(i) then 2 EXP i else 0)
       ==> !i. i <= n ==> (b(i) <=> c(i))`;;

let COUNTABLE_REPEATING = `countable repeating`;;

(* ------------------------------------------------------------------------- *)
(* Canonical digits and their uncountability.                                *)
(* ------------------------------------------------------------------------- *)

let canonical = new_definition
 `canonical = {s:num->bool | !n. ?m. m >= n /\ ~(s m)}`;;

let UNCOUNTABLE_CANONICAL = `~countable canonical`;;

(* ------------------------------------------------------------------------- *)
(* Injection of canonical digits into the reals.                             *)
(* ------------------------------------------------------------------------- *)

needs "Library/analysis.ml";;

prioritize_real();;

let SUM_BINSEQUENCE_LBOUND = `!m n. &0 <= sum(m,n) (\i. if s(i) then inv(&2 pow i) else &0)`;;

let SUM_BINSEQUENCE_UBOUND_SHARP = `!s m n. sum(m,n) (\i. if s(i) then inv(&2 pow i) else &0)
             <= &2 / &2 pow m - &2 / &2 pow (m + n)`;;

let SUMMABLE_BINSEQUENCE = `!s. summable (\i. if s(i) then inv(&2 pow i) else &0)`;;

let SUMS_BINSEQUENCE = `!s. (\i. if s(i) then inv(&2 pow i) else &0) sums
       (suminf (\i. if s(i) then inv(&2 pow i) else &0))`;;

let SUM_BINSEQUENCE_UBOUND_LE = `!s m n. sum(m,n) (\i. if s(i) then inv(&2 pow i) else &0) <= &2 / &2 pow m`;;

(* ------------------------------------------------------------------------- *)
(* The main injection and hence main theorem.                                *)
(* ------------------------------------------------------------------------- *)

let SUMINF_INJ_LEMMA = `!s t n. ~(s n) /\ t n /\
           (!m. m < n ==> (s(m) <=> t(m))) /\
           (!n. ?m. m >= n /\ ~(s m))
           ==> suminf(\n. if s n then inv (&2 pow n) else &0)
                < suminf(\n. if t n then inv (&2 pow n) else &0)`;;

let UNCOUNTABLE_REALS = `~countable(UNIV:real->bool)`;;
