(* ========================================================================= *)
(* Representation of primes == 1 (mod 4) as sum of 2 squares.                *)
(* ========================================================================= *)

needs "Library/prime.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Definition of involution and various basic lemmas.                        *)
(* ------------------------------------------------------------------------- *)

let involution = new_definition
  `involution f s = !x. x IN s ==> f(x) IN s /\ (f(f(x)) = x)`;;

let INVOLUTION_IMAGE = `!f s. involution f s ==> (IMAGE f s = s)`;;

let INVOLUTION_DELETE = `involution f s /\ a IN s /\ (f a = a) ==> involution f (s DELETE a)`;;

let INVOLUTION_STEPDOWN = `involution f s /\ a IN s ==> involution f (s DIFF {a, (f a)})`;;

let INVOLUTION_NOFIXES = `involution f s ==> involution f {x | x IN s /\ ~(f x = x)}`;;

let INVOLUTION_SUBSET = `!f s t. involution f s /\ (!x. x IN t ==> f(x) IN t) /\ t SUBSET s
           ==> involution f t`;;

let INVOLUTION_EVEN = `!s. FINITE(s) /\ involution f s /\ (!x:A. x IN s ==> ~(f x = x))
       ==> EVEN(CARD s)`;;

(* ------------------------------------------------------------------------- *)
(* So an involution with exactly one fixpoint has odd card domain.           *)
(* ------------------------------------------------------------------------- *)

let INVOLUTION_FIX_ODD = `FINITE(s) /\ involution f s /\ (?!a:A. a IN s /\ (f a = a))
   ==> ODD(CARD s)`;;

(* ------------------------------------------------------------------------- *)
(* And an involution on a set of odd finite card must have a fixpoint.       *)
(* ------------------------------------------------------------------------- *)

let INVOLUTION_ODD = `!n s. FINITE(s) /\ involution f s /\ ODD(CARD s)
         ==> ?a. a IN s /\ (f a = a)`;;

(* ------------------------------------------------------------------------- *)
(* Consequently, if one involution has a unique fixpoint, other has one.     *)
(* ------------------------------------------------------------------------- *)

let INVOLUTION_FIX_FIX = `!f g s. FINITE(s) /\ involution f s /\ involution g s /\
           (?!x. x IN s /\ (f x = x)) ==> ?x. x IN s /\ (g x = x)`;;

(* ------------------------------------------------------------------------- *)
(* Formalization of Zagier's "one-sentence" proof over the natural numbers.  *)
(* ------------------------------------------------------------------------- *)

let zset = new_definition
  `zset(a) = {(x,y,z) | x EXP 2 + 4 * y * z = a}`;;

let zag = new_definition
  `zag(x,y,z) =
        if x + z < y then (x + 2 * z,z,y - (x + z))
        else if x < 2 * y then (2 * y - x, y, (x + z) - y)
        else (x - 2 * y,(x + z) - y, y)`;;

let tag = new_definition
  `tag((x,y,z):num#num#num) = (x,z,y)`;;

let ZAG_INVOLUTION_GENERAL = `0 < x /\ 0 < y /\ 0 < z ==> (zag(zag(x,y,z)) = (x,y,z))`;;

let IN_TRIPLE = `(a,b,c) IN {(x,y,z) | P x y z} <=> P a b c`;;

let PRIME_SQUARE = `!n. ~prime(n * n)`;;

let PRIME_4X = `!n. ~prime(4 * n)`;;

let PRIME_XYZ_NONZERO = `prime(x EXP 2 + 4 * y * z) ==> 0 < x /\ 0 < y /\ 0 < z`;;

let ZAG_INVOLUTION = `!p. prime(p) ==> involution zag (zset(p))`;;

let TAG_INVOLUTION = `!a. involution tag (zset a)`;;

let ZAG_LEMMA = `(zag(x,y,z) = (x,y,z)) ==> (y = x)`;;

let ZSET_BOUND = `0 < y /\ 0 < z /\ (x EXP 2 + 4 * y * z = p)
   ==> x <= p /\ y <= p /\ z <= p`;;

let ZSET_FINITE = `!p. prime(p) ==> FINITE(zset p)`;;

let SUM_OF_TWO_SQUARES = `!p k. prime(p) /\ (p = 4 * k + 1) ==> ?x y. p = x EXP 2 + y EXP 2`;;
