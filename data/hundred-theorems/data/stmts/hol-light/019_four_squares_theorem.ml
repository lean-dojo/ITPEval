(* ========================================================================= *)
(* Theorems about representations as sums of 2 and 4 squares.                *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/analysis.ml";; (*** only for REAL_ARCH_LEAST! ***)

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

(* ------------------------------------------------------------------------- *)
(* General pigeonhole lemma.                                                 *)
(* ------------------------------------------------------------------------- *)

let PIGEONHOLE_LEMMA = `!f:A->B g s t.
        FINITE(s) /\ FINITE(t) /\
        (!x. x IN s ==> f(x) IN t) /\
        (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) /\
        (!x. x IN s ==> g(x) IN t) /\
        (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y)) /\
        CARD(t) < 2 * CARD(s)
        ==> ?x y. x IN s /\ y IN s /\ (f x = g y)`;;

(* ------------------------------------------------------------------------- *)
(* In particular, consider functions out of 0...(p-1)/2, mod p.              *)
(* ------------------------------------------------------------------------- *)

let PIGEONHOLE_LEMMA_P12 = `!f g p.
        ODD(p) /\
        (!x. 2 * x < p ==> f(x) < p) /\
        (!x y. 2 * x < p /\ 2 * y < p /\ (f x = f y) ==> (x = y)) /\
        (!x. 2 * x < p ==> g(x) < p) /\
        (!x y. 2 * x < p /\ 2 * y < p /\ (g x = g y) ==> (x = y))
        ==> ?x y. 2 * x < p /\ 2 * y < p /\ (f x = g y)`;;

(* ------------------------------------------------------------------------- *)
(* Show that \x. x^2 + a (mod p) satisfies the conditions.                   *)
(* ------------------------------------------------------------------------- *)

let SQUAREMOD_INJ_LEMMA = `!p x d. prime(p) /\ 2 * (x + d) < p /\
           ((x + d) * (x + d) + m * p = x * x + n * p)
           ==> (d = 0)`;;

let SQUAREMOD_INJ = `!p. prime(p)
   ==> (!x. 2 * x < p ==> (x EXP 2 + a) MOD p < p) /\
       (!x y. 2 * x < p /\ 2 * y < p /\
              ((x EXP 2 + a) MOD p = (y EXP 2 + a) MOD p)
              ==> (x = y))`;;

(* ------------------------------------------------------------------------- *)
(* Show that also a reflection mod p retains this property.                  *)
(* ------------------------------------------------------------------------- *)

let REFLECT_INJ = `(!x. 2 * x < p ==> f(x) < p) /\
   (!x y. 2 * x < p /\ 2 * y < p /\ (f x = f y) ==> (x = y))
   ==> (!x. 2 * x < p ==> p - 1 - f(x) < p) /\
       (!x y. 2 * x < p /\ 2 * y < p /\ (p - 1 - f(x) = p - 1 - f(y))
              ==> (x = y))`;;

(* ------------------------------------------------------------------------- *)
(* Hence the main result.                                                    *)
(* ------------------------------------------------------------------------- *)

let LAGRANGE_LEMMA_ODD = `!a p. prime(p) /\ ODD(p)
         ==> ?n x y. 2 * x < p /\ 2 * y < p /\
                     (n * p = x EXP 2 + y EXP 2 + a + 1)`;;

(* ------------------------------------------------------------------------- *)
(* Avoid the additional conditions.                                          *)
(* ------------------------------------------------------------------------- *)

let LAGRANGE_LEMMA = `!a p. prime(p)
         ==> ?n x y. 2 * x <= p /\ 2 * y <= p /\
                     (n * p = x EXP 2 + y EXP 2 + a)`;;

(* ------------------------------------------------------------------------- *)
(* Aubrey's lemma showing that rationals suffice for sums of 4 squares.      *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let REAL_INTEGER_CLOSURES = `(!n. ?p. abs(&n) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x + y) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x - y) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x * y) = &p) /\
   (!x r. (?n. abs(x) = &n) ==> ?p. abs(x pow r) = &p) /\
   (!x. (?n. abs(x) = &n) ==> ?p. abs(--x) = &p) /\
   (!x. (?n. abs(x) = &n) ==> ?p. abs(abs x) = &p)`;;

let REAL_NUM_ROUND = `!x. &0 <= x ==> ?n. abs(x - &n) <= &1 / &2`;;

let REAL_POS_ABS_MIDDLE = `!x n. &0 <= x /\ (abs(x - &n) = &1 / &2)
         ==> (x = &(n - 1) + &1 / &2) \/ (x = &n + &1 / &2)`;;

let REAL_RAT_ABS_MIDDLE = `!m n p. (abs(&m / &p - &n) = &1 / &2)
         ==> (&m / &p = &(n - 1) + &1 / &2) \/ (&m / &p = &n + &1 / &2)`;;

let AUBREY_LEMMA_4 = `!m n p q r.
        ~(m = 0) /\ ~(m = 1) /\
        ((&n / &m) pow 2 + (&p / &m) pow 2 +
         (&q / &m) pow 2 + (&r / &m) pow 2 = &N)
        ==> ?m' n' p' q' r'.
               ~(m' = 0) /\ m' < m /\
               ((&n' / &m') pow 2 + (&p' / &m') pow 2 +
                (&q' / &m') pow 2 + (&r' / &m') pow 2 = &N)`;;

(* ------------------------------------------------------------------------- *)
(* Hence the main result.                                                    *)
(* ------------------------------------------------------------------------- *)

let AUBREY_THM_4 = `(?q. ~(q = 0) /\
       ?a b c d.
            (&a / &q) pow 2 + (&b / &q) pow 2 +
            (&c / &q) pow 2 + (&d / &q) pow 2 = &N)
   ==> ?a b c d. &a pow 2 + &b pow 2 + &c pow 2 + &d pow 2 = &N`;;

(* ------------------------------------------------------------------------- *)
(* The algebraic lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let LAGRANGE_IDENTITY = REAL_ARITH
  `(w1 pow 2 + x1 pow 2 + y1 pow 2 + z1 pow 2) *
   (w2 pow 2 + x2 pow 2 + y2 pow 2 + z2 pow 2) =
   (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) pow 2 +
   (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) pow 2 +
   (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) pow 2 +
   (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2) pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Now sum of 4 squares.                                                     *)
(* ------------------------------------------------------------------------- *)

let LAGRANGE_REAL_NUM = `!n. ?w x y z. &n = &w pow 2 + &x pow 2 + &y pow 2 + &z pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Also prove it for the natural numbers.                                    *)
(* ------------------------------------------------------------------------- *)

let LAGRANGE_NUM = `!n. ?w x y z. n = w EXP 2 + x EXP 2 + y EXP 2 + z EXP 2`;;

(* ------------------------------------------------------------------------- *)
(* And for the integers.                                                     *)
(* ------------------------------------------------------------------------- *)

prioritize_int();;

let LAGRANGE_INT = `!a. &0 <= a <=> ?w x y z. a = w pow 2 + x pow 2 + y pow 2 + z pow 2`;;

prioritize_num();;
