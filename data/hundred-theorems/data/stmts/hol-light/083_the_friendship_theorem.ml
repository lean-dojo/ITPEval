(* ========================================================================= *)
(* The friendship theorem.                                                   *)
(*                                                                           *)
(* Proof from "Combinatorics Tutorial 2: Friendship Theorem", copyright      *)
(* MathOlymp.com, 2001. Apparently due to J. Q. Longyear and T. D. Parsons.  *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/pocklington.ml";;

(* ------------------------------------------------------------------------- *)
(* Useful inductive breakdown principle ending at gcd.                       *)
(* ------------------------------------------------------------------------- *)

let GCD_INDUCT = `!P. (!m n. P m /\ P (m + n) ==> P n)
       ==> !m n. P m /\ P n ==> P (gcd(m,n))`;;

(* ------------------------------------------------------------------------- *)
(* General theorems about loops in a sequence.                               *)
(* ------------------------------------------------------------------------- *)

let LOOP_GCD = `!x m n. (!i. x(i + m) = x(i)) /\ (!i. x(i + n) = x(i))
           ==> !i. x(i + gcd(m,n)) = x(i)`;;

let LOOP_COPRIME = `!x m n. (!i. x(i + m) = x(i)) /\ (!i. x(i + n) = x(i)) /\ coprime(m,n)
           ==> !i. x i = x 0`;;

(* ------------------------------------------------------------------------- *)
(* General theorem about partition into equally-sized eqv classes.           *)
(* ------------------------------------------------------------------------- *)

let EQUIVALENCE_UNIFORM_PARTITION = `!R s k. FINITE s /\
           (!x. x IN s ==> R x x) /\
           (!x y. R x y ==> R y x) /\
           (!x y z. R x y /\ R y z ==> R x z) /\
           (!x:A. x IN s ==> CARD {y | y IN s /\ R x y} = k)
           ==> k divides (CARD s)`;;

(* ------------------------------------------------------------------------- *)
(* With explicit restricted quantification.                                  *)
(* ------------------------------------------------------------------------- *)

let EQUIVALENCE_UNIFORM_PARTITION_RESTRICT = `!R s k. FINITE s /\
           (!x. x IN s ==> R x x) /\
           (!x y. x IN s /\ y IN s /\ R x y ==> R y x) /\
           (!x y z. x IN s /\ y IN s /\ z IN s /\ R x y /\ R y z ==> R x z) /\
           (!x:A. x IN s ==> CARD {y | y IN s /\ R x y} = k)
           ==> k divides (CARD s)`;;

(* ------------------------------------------------------------------------- *)
(* General theorem about pairing up elements of a set.                       *)
(* ------------------------------------------------------------------------- *)

let ELEMENTS_PAIR_UP = `!s r. FINITE s /\
         (!x. x IN s ==> ~(r x x)) /\
         (!x y. x IN s /\ y IN s /\ r x y ==> r y x) /\
         (!x:A. x IN s ==> ?!y. y IN s /\ r x y)
         ==> EVEN(CARD s)`;;

(* ------------------------------------------------------------------------- *)
(* Cycles and paths.                                                         *)
(* ------------------------------------------------------------------------- *)

let cycle = new_definition
 `cycle r k x <=> (!i. r (x i) (x(i + 1))) /\ (!i. x(i + k) = x(i))`;;

let path = new_definition
 `path r k x <=> (!i. i < k ==> r (x i) (x(i + 1))) /\
                 (!i. k < i ==> x(i) = @x. T)`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about these concepts.                                              *)
(* ------------------------------------------------------------------------- *)

let CYCLE_OFFSET = `!r k x:num->A. cycle r k x ==> !i m. x(m * k + i) = x(i)`;;

let CYCLE_MOD = `!r k x:num->A. cycle r k x /\ ~(k = 0) ==> !i. x(i MOD k) = x(i)`;;

let PATHS_MONO = `(!x y. r x y ==> s x y) ==> {x | path r k x} SUBSET {x | path s k x}`;;

let HAS_SIZE_PATHS = `!N m r k. (:A) HAS_SIZE N /\ (!x. {y | r x y} HAS_SIZE m)
             ==> {x:num->A | path r k x} HAS_SIZE (N * m EXP k)`;;

let FINITE_PATHS = `!r k. FINITE(:A) ==> FINITE {x:num->A | path r k x}`;;

let HAS_SIZE_CYCLES = `!r k. FINITE(:A) /\ ~(k = 0)
         ==> {x:num->A | cycle r k x} HAS_SIZE
             CARD{x:num->A | path r k x /\ x(k) = x(0)}`;;

let FINITE_CYCLES = `!r k. FINITE(:A) /\ ~(k = 0) ==> FINITE {x:num->A | cycle r k x}`;;

let CARD_PATHCYCLES_STEP = `!N m r k.
     (:A) HAS_SIZE N /\ ~(k = 0) /\ ~(m = 0) /\
     (!x:A. {y | r x y} HAS_SIZE m) /\
     (!x y. r x y ==> r y x) /\
     (!x y. ~(x = y) ==> ?!z. r x z /\ r z y)
     ==> {x | path r (k + 2) x /\ x(k + 2) = x(0)} HAS_SIZE
         (m * CARD {x | path r k x /\ x(k) = x(0)} +
          CARD {x | path r (k) x /\ ~(x(k) = x(0))})`;;

(* ------------------------------------------------------------------------- *)
(* The first lemma about the number of cycles.                               *)
(* ------------------------------------------------------------------------- *)

let shiftable = new_definition
 `shiftable x y <=> ?k. !i. x(i) = y(i + k)`;;

let SHIFTABLE_REFL = `!x. shiftable x x`;;

let SHIFTABLE_TRANS = `!x y z. shiftable x y /\ shiftable y z ==> shiftable x z`;;

let SHIFTABLE_LOCAL = `!x y p r. cycle r p x /\ cycle r p y /\ ~(p = 0)
             ==> (shiftable x y <=> ?k. k < p /\ !i. x(i) = y(i + k))`;;

let SHIFTABLE_SYM = `!x y p r. cycle r p x /\ cycle r p y /\ ~(p = 0) /\ shiftable x y
             ==> shiftable y x`;;

let CYCLES_PRIME_LEMMA = `!r p x. FINITE(:A) /\ prime p /\ (!x. ~(r x x))
           ==> p divides CARD {x:num->A | cycle r p x}`;;

(* ------------------------------------------------------------------------- *)
(* The theorem itself.                                                       *)
(* ------------------------------------------------------------------------- *)

let FRIENDSHIP = `!friend:person->person->bool.
      FINITE(:person) /\
      (!x. ~(friend x x)) /\
      (!x y. friend x y ==> friend y x) /\
      (!x y. ~(x = y) ==> ?!z. friend x z /\ friend y z)
      ==> ?u. !v. ~(v = u) ==> friend u v`;;
