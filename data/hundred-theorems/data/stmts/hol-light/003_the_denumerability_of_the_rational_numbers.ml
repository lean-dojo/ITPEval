(* ========================================================================= *)
(* Theorem 3: countability of rational numbers.                              *)
(* ========================================================================= *)

needs "Library/card.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Definition of rational and countable.                                     *)
(* ------------------------------------------------------------------------- *)

let rational = new_definition
  `rational(r) <=> ?p q. ~(q = 0) /\ (abs(r) = &p / &q)`;;

let countable = new_definition
  `countable s <=> s <=_c (UNIV:num->bool)`;;

(* ------------------------------------------------------------------------- *)
(* Proof of the main result.                                                 *)
(* ------------------------------------------------------------------------- *)

let COUNTABLE_RATIONALS = `countable { x:real | rational(x)}`;;

(* ------------------------------------------------------------------------- *)
(* Maybe I should actually prove equality?                                   *)
(* ------------------------------------------------------------------------- *)

let denumerable = new_definition
  `denumerable s <=> s =_c (UNIV:num->bool)`;;

let DENUMERABLE_RATIONALS = `denumerable { x:real | rational(x)}`;;

(* ------------------------------------------------------------------------- *)
(* Expand out the cardinal comparison definitions for explicitness.          *)
(* ------------------------------------------------------------------------- *)

let DENUMERABLE_RATIONALS_EXPAND = `?rat:num->real. (!n. rational(rat n)) /\
                   (!x. rational x ==> ?!n. x = rat n)`;;
