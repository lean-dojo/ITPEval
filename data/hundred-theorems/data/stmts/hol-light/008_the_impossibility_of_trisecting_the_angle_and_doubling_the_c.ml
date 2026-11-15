(* ========================================================================= *)
(* Non-constructibility of irrational cubic equation solutions.              *)
(*                                                                           *)
(* This gives the two classic impossibility results: trisecting an angle or  *)
(* constructing the cube using traditional geometric constructions.          *)
(*                                                                           *)
(* This elementary proof (not using field extensions etc.) is taken from     *)
(* Dickson's "First Course in the Theory of Equations", chapter III.         *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/floor.ml";;
needs "Multivariate/transcendentals.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* The critical lemma.                                                       *)
(* ------------------------------------------------------------------------- *)

let STEP_LEMMA = `!P. (!n. P(&n)) /\
       (!x. P x ==> P(--x)) /\
       (!x. P x /\ ~(x = &0) ==> P(inv x)) /\
       (!x y. P x /\ P y ==> P(x + y)) /\
       (!x y. P x /\ P y ==> P(x * y))
       ==> !a b c z u v s.
               P a /\ P b /\ P c /\
               z pow 3 + a * z pow 2 + b * z + c = &0 /\
               P u /\ P v /\ P(s * s) /\ z = u + v * s
               ==> ?w. P w /\ w pow 3 + a * w pow 2 + b * w + c = &0`;;

(* ------------------------------------------------------------------------- *)
(* Instantiate to square roots.                                              *)
(* ------------------------------------------------------------------------- *)

let STEP_LEMMA_SQRT = `!P. (!n. P(&n)) /\
       (!x. P x ==> P(--x)) /\
       (!x. P x /\ ~(x = &0) ==> P(inv x)) /\
       (!x y. P x /\ P y ==> P(x + y)) /\
       (!x y. P x /\ P y ==> P(x * y))
       ==> !a b c z u v s.
               P a /\ P b /\ P c /\
               z pow 3 + a * z pow 2 + b * z + c = &0 /\
               P u /\ P v /\ P(s) /\ &0 <= s /\ z = u + v * sqrt(s)
               ==> ?w. P w /\ w pow 3 + a * w pow 2 + b * w + c = &0`;;

(* ------------------------------------------------------------------------- *)
(* Numbers definable by radicals involving square roots only.                *)
(* ------------------------------------------------------------------------- *)

let radical_RULES,radical_INDUCT,radical_CASES = new_inductive_definition
 `(!x. rational x ==> radical x) /\
  (!x. radical x ==> radical (--x)) /\
  (!x. radical x /\ ~(x = &0) ==> radical (inv x)) /\
  (!x y. radical x /\ radical y ==> radical (x + y)) /\
  (!x y. radical x /\ radical y ==> radical (x * y)) /\
  (!x. radical x /\ &0 <= x ==> radical (sqrt x))`;;

let RADICAL_RULES = `(!n. radical(&n)) /\
   (!x. rational x ==> radical x) /\
   (!x. radical x ==> radical (--x)) /\
   (!x. radical x /\ ~(x = &0) ==> radical (inv x)) /\
   (!x y. radical x /\ radical y ==> radical (x + y)) /\
   (!x y. radical x /\ radical y ==> radical (x - y)) /\
   (!x y. radical x /\ radical y ==> radical (x * y)) /\
   (!x y. radical x /\ radical y /\ ~(y = &0) ==> radical (x / y)) /\
   (!x n. radical x ==> radical(x pow n)) /\
   (!x. radical x /\ &0 <= x ==> radical (sqrt x))`;;

let RADICAL_TAC =
  REPEAT(MATCH_ACCEPT_TAC (CONJUNCT1 RADICAL_RULES) ORELSE
         (MAP_FIRST MATCH_MP_TAC(tl(tl(CONJUNCTS RADICAL_RULES))) THEN
          REPEAT CONJ_TAC));;

(* ------------------------------------------------------------------------- *)
(* Explicit "expressions" to support inductive proof.                        *)
(* ------------------------------------------------------------------------- *)

let expression_INDUCT,expression_RECURSION = define_type
 "expression = Constant real
             | Negation expression
             | Inverse expression
             | Addition expression expression
             | Multiplication expression expression
             | Sqrt expression";;

(* ------------------------------------------------------------------------- *)
(* Interpretation.                                                           *)
(* ------------------------------------------------------------------------- *)

let value = define
 `(value(Constant x) = x) /\
  (value(Negation e) = --(value e)) /\
  (value(Inverse e) = inv(value e)) /\
  (value(Addition e1 e2) = value e1 + value e2) /\
  (value(Multiplication e1 e2) = value e1 * value e2) /\
  (value(Sqrt e) = sqrt(value e))`;;

(* ------------------------------------------------------------------------- *)
(* Wellformedness of an expression.                                          *)
(* ------------------------------------------------------------------------- *)

let wellformed = define
 `(wellformed(Constant x) <=> rational x) /\
  (wellformed(Negation e) <=> wellformed e) /\
  (wellformed(Inverse e) <=> ~(value e = &0) /\ wellformed e) /\
  (wellformed(Addition e1 e2) <=> wellformed e1 /\ wellformed e2) /\
  (wellformed(Multiplication e1 e2) <=> wellformed e1 /\ wellformed e2) /\
  (wellformed(Sqrt e) <=> &0 <= value e /\ wellformed e)`;;

(* ------------------------------------------------------------------------- *)
(* The set of radicals in an expression.                                     *)
(* ------------------------------------------------------------------------- *)

let radicals = define
 `(radicals(Constant x) = {}) /\
  (radicals(Negation e) = radicals e) /\
  (radicals(Inverse e) = radicals e) /\
  (radicals(Addition e1 e2) = (radicals e1) UNION (radicals e2)) /\
  (radicals(Multiplication e1 e2) = (radicals e1) UNION (radicals e2)) /\
  (radicals(Sqrt e) = e INSERT (radicals e))`;;

let FINITE_RADICALS = `!e. FINITE(radicals e)`;;

let WELLFORMED_RADICALS = `!e. wellformed e ==> !r. r IN radicals(e) ==> &0 <= value r`;;

let RADICALS_WELLFORMED = `!e. wellformed e ==> !r. r IN radicals e ==> wellformed r`;;

let RADICALS_SUBSET = `!e r. r IN radicals e ==> radicals(r) SUBSET radicals(e)`;;

(* ------------------------------------------------------------------------- *)
(* Show that every radical is the interpretation of a wellformed expresion.  *)
(* ------------------------------------------------------------------------- *)

let RADICAL_EXPRESSION = `!x. radical x <=> ?e. wellformed e /\ x = value e`;;

(* ------------------------------------------------------------------------- *)
(* Nesting depth of radicals in an expression.                               *)
(* ------------------------------------------------------------------------- *)

let LT_MAX = `!a b c. a < MAX b c <=> a < b \/ a < c`;;

let depth = define
 `(depth(Constant x) = 0) /\
  (depth(Negation e) = depth e) /\
  (depth(Inverse e) = depth e) /\
  (depth(Addition e1 e2) = MAX (depth e1) (depth e2)) /\
  (depth(Multiplication e1 e2) = MAX (depth e1) (depth e2)) /\
  (depth(Sqrt e) = 1 + depth e)`;;

let IN_RADICALS_SMALLER = `!r s. s IN radicals(r) ==> depth(s) < depth(r)`;;

let NOT_IN_OWN_RADICALS = `!r. ~(r IN radicals r)`;;

let RADICALS_EMPTY_RATIONAL = `!e. wellformed e /\ radicals e = {} ==> rational(value e)`;;

(* ------------------------------------------------------------------------- *)
(* Crucial point about splitting off some "topmost" radical.                 *)
(* ------------------------------------------------------------------------- *)

let FINITE_MAX = `!s. FINITE s ==> ~(s = {}) ==> ?b:num. b IN s /\ !a. a IN s ==> a <= b`;;

let RADICAL_TOP = `!e. ~(radicals e = {})
       ==> ?r. r IN radicals e /\
               !s. s IN radicals(e) ==> ~(r IN radicals s)`;;

(* ------------------------------------------------------------------------- *)
(* By rearranging the expression we can use it in a canonical way.           *)
(* ------------------------------------------------------------------------- *)

let RADICAL_CANONICAL_TRIVIAL = `!e r.
     (r IN radicals e
            ==> (?a b.
                   wellformed a /\
                   wellformed b /\
                   value e = value a + value b * sqrt (value r) /\
                   radicals a SUBSET radicals e DELETE r /\
                   radicals b SUBSET radicals e DELETE r /\
                   radicals r SUBSET radicals e DELETE r))
     ==> wellformed e
         ==> ?a b. wellformed a /\
                   wellformed b /\
                   value e = value a + value b * sqrt (value r) /\
                   radicals a SUBSET (radicals e UNION radicals r) DELETE r /\
                   radicals b SUBSET (radicals e UNION radicals r) DELETE r /\
                   radicals r SUBSET (radicals e UNION radicals r) DELETE r`;;

let RADICAL_CANONICAL = `!e. wellformed e /\ ~(radicals e = {})
       ==> ?r. r IN radicals(e) /\
               ?a b. wellformed(Addition a (Multiplication b (Sqrt r))) /\
                     value e = value(Addition a (Multiplication b (Sqrt r))) /\
                     (radicals a) SUBSET (radicals(e) DELETE r) /\
                     (radicals b) SUBSET (radicals(e) DELETE r) /\
                     (radicals r) SUBSET (radicals(e) DELETE r)`;;

(* ------------------------------------------------------------------------- *)
(* Now we quite easily get an inductive argument.                            *)
(* ------------------------------------------------------------------------- *)

let CUBIC_ROOT_STEP = `!a b c. rational a /\ rational b /\ rational c
           ==> !e. wellformed e /\
                   ~(radicals e = {}) /\
                   (value e) pow 3 + a * (value e) pow 2 +
                                     b * (value e) + c = &0
                   ==> ?e'. wellformed e' /\
                            (radicals e') PSUBSET (radicals e) /\
                            (value e') pow 3 + a * (value e') pow 2 +
                                     b * (value e') + c = &0`;;

(* ------------------------------------------------------------------------- *)
(* Hence the main result.                                                    *)
(* ------------------------------------------------------------------------- *)

let CUBIC_ROOT_RADICAL_INDUCT = `!a b c. rational a /\ rational b /\ rational c
           ==> !n e. wellformed e /\ CARD (radicals e) = n /\
                     (value e) pow 3 + a * (value e) pow 2 +
                                b * (value e) + c = &0
                 ==> ?x. rational x /\
                         x pow 3 + a * x pow 2 + b * x + c = &0`;;

let CUBIC_ROOT_RATIONAL = `!a b c. rational a /\ rational b /\ rational c /\
           (?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0)
           ==> (?x. rational x /\ x pow 3 + a * x pow 2 + b * x + c = &0)`;;

(* ------------------------------------------------------------------------- *)
(* Now go further to an *integer*, since the polynomial is monic.            *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;

let RATIONAL_LOWEST_LEMMA = `!p q. ~(q = 0) ==> ?p' q'. ~(q' = 0) /\ coprime(p',q') /\ p * q' = p' * q`;;

prioritize_real();;

let RATIONAL_LOWEST = `!x. rational x <=> ?p q. ~(q = 0) /\ coprime(p,q) /\ abs(x) = &p / &q`;;

let RATIONAL_ROOT_INTEGER = `!a b c x. integer a /\ integer b /\ integer c /\ rational x /\
             x pow 3 + a * x pow 2 + b * x + c = &0
             ==> integer x`;;

(* ------------------------------------------------------------------------- *)
(* Hence we have our big final theorem.                                      *)
(* ------------------------------------------------------------------------- *)

let CUBIC_ROOT_INTEGER = `!a b c. integer a /\ integer b /\ integer c /\
           (?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0)
           ==> (?x. integer x /\ x pow 3 + a * x pow 2 + b * x + c = &0)`;;

(* ------------------------------------------------------------------------- *)
(* Geometrical definitions.                                                  *)
(* ------------------------------------------------------------------------- *)

let length = new_definition
  `length(a:real^2,b:real^2) = norm(b - a)`;;

let parallel = new_definition
 `parallel (a:real^2,b:real^2) (c:real^2,d:real^2) <=>
        (a$1 - b$1) * (c$2 - d$2) = (a$2 - b$2) * (c$1 - d$1)`;;

let collinear3 = new_definition
  `collinear3 (a:real^2) b c <=> parallel (a,b) (a,c)`;;

let is_intersection = new_definition
  `is_intersection p (a,b) (c,d) <=> collinear3 a p b /\ collinear3 c p d`;;

let on_circle = new_definition
 `on_circle x (centre,pt) <=> length(centre,x) = length(centre,pt)`;;

(* ------------------------------------------------------------------------- *)
(* A trivial lemma.                                                          *)
(* ------------------------------------------------------------------------- *)

let SQRT_CASES_LEMMA = `!x y. y pow 2 = x ==> &0 <= x /\ (sqrt(x) = y \/ sqrt(x) = --y)`;;

(* ------------------------------------------------------------------------- *)
(* Show that solutions to certain classes of equations are radical.          *)
(* ------------------------------------------------------------------------- *)

let RADICAL_LINEAR_EQUATION = `!a b x. radical a /\ radical b /\ ~(a = &0 /\ b = &0) /\ a * x + b = &0
           ==> radical x`;;

let RADICAL_SIMULTANEOUS_LINEAR_EQUATION = `!a b c d e f x.
        radical a /\ radical b /\ radical c /\
        radical d /\ radical e /\ radical f /\
        ~(a * e = b * d /\ a * f = c * d /\ e * c = b * f) /\
        a * x + b * y = c /\ d * x + e * y = f
        ==> radical(x) /\ radical(y)`;;

let RADICAL_QUADRATIC_EQUATION = `!a b c x. radical a /\ radical b /\ radical c /\
             a * x pow 2 + b * x + c = &0 /\
             ~(a = &0 /\ b = &0 /\ c = &0)
             ==> radical x`;;

let RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC = `!a b c d e f x.
        radical a /\ radical b /\ radical c /\
        radical d /\ radical e /\ radical f /\
        ~(d = &0 /\ e = &0 /\ f = &0) /\
        (x - a) pow 2 + (y - b) pow 2 = c /\ d * x + e * y = f
        ==> radical x /\ radical y`;;

let RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC = `!a b c d e f x.
        radical a /\ radical b /\ radical c /\
        radical d /\ radical e /\ radical f /\
        ~(a = d /\ b = e /\ c = f) /\
        (x - a) pow 2 + (y - b) pow 2 = c /\
        (x - d) pow 2 + (y - e) pow 2 = f
        ==> radical x /\ radical y`;;

(* ------------------------------------------------------------------------- *)
(* Analytic criterion for constructibility.                                  *)
(* ------------------------------------------------------------------------- *)

let constructible_RULES,constructible_INDUCT,constructible_CASES =
 new_inductive_definition
  `(!x:real^2. rational(x$1) /\ rational(x$2) ==> constructible x) /\
// Intersection of two non-parallel lines AB and CD
  (!a b c d x. constructible a /\ constructible b /\
               constructible c /\ constructible d /\
               ~parallel (a,b) (c,d) /\ is_intersection x (a,b) (c,d)
               ==> constructible x) /\
// Intersection of a nontrivial line AB and circle with centre C, radius DE
  (!a b c d e x. constructible a /\ constructible b /\
                 constructible c /\ constructible d /\
                 constructible e /\
                 ~(a = b) /\ collinear3 a x b /\ length (c,x) = length(d,e)
                 ==> constructible x) /\
// Intersection of distinct circles with centres A and D, radii BD and EF
  (!a b c d e f x. constructible a /\ constructible b /\
                   constructible c /\ constructible d /\
                   constructible e /\ constructible f /\
                   ~(a = d /\ length (b,c) = length (e,f)) /\
                   length (a,x) = length (b,c) /\ length (d,x) = length (e,f)
                   ==> constructible x)`;;

(* ------------------------------------------------------------------------- *)
(* Some "coordinate geometry" lemmas.                                        *)
(* ------------------------------------------------------------------------- *)

let RADICAL_LINE_LINE_INTERSECTION = `!a b c d x.
        radical(a$1) /\ radical(a$2) /\
        radical(b$1) /\ radical(b$2) /\
        radical(c$1) /\ radical(c$2) /\
        radical(d$1) /\ radical(d$2) /\
        ~(parallel (a,b) (c,d)) /\ is_intersection x (a,b) (c,d)
        ==> radical(x$1) /\ radical(x$2)`;;

let RADICAL_LINE_CIRCLE_INTERSECTION = `!a b c d e x.
        radical(a$1) /\ radical(a$2) /\
        radical(b$1) /\ radical(b$2) /\
        radical(c$1) /\ radical(c$2) /\
        radical(d$1) /\ radical(d$2) /\
        radical(e$1) /\ radical(e$2) /\
        ~(a = b) /\ collinear3 a x b /\ length(c,x) = length(d,e)
        ==> radical(x$1) /\ radical(x$2)`;;

let RADICAL_CIRCLE_CIRCLE_INTERSECTION = `!a b c d e f x.
        radical(a$1) /\ radical(a$2) /\
        radical(b$1) /\ radical(b$2) /\
        radical(c$1) /\ radical(c$2) /\
        radical(d$1) /\ radical(d$2) /\
        radical(e$1) /\ radical(e$2) /\
        radical(f$1) /\ radical(f$2) /\
        length(a,x) = length(b,c) /\
        length(d,x) = length(e,f) /\
        ~(a = d /\ length(b,c) = length(e,f))
        ==> radical(x$1) /\ radical(x$2)`;;

(* ------------------------------------------------------------------------- *)
(* So constructible points have radical coordinates.                         *)
(* ------------------------------------------------------------------------- *)

let CONSTRUCTIBLE_RADICAL = `!x. constructible x ==> radical(x$1) /\ radical(x$2)`;;

(* ------------------------------------------------------------------------- *)
(* Impossibility of doubling the cube.                                       *)
(* ------------------------------------------------------------------------- *)

let DOUBLE_THE_CUBE_ALGEBRA = `~(?x. radical x /\ x pow 3 = &2)`;;

let DOUBLE_THE_CUBE = `!x. x pow 3 = &2 ==> ~(constructible(vector[x; &0]))`;;

(* ------------------------------------------------------------------------- *)
(* Impossibility of trisecting                                               *)
(* ------------------------------------------------------------------------- *)

let COS_TRIPLE = `!x. cos(&3 * x) = &4 * cos(x) pow 3 - &3 * cos(x)`;;

let COS_PI3 = `cos(pi / &3) = &1 / &2`;;

let TRISECT_60_DEGREES_ALGEBRA = `~(?x. radical x /\ x pow 3 - &3 * x - &1 = &0)`;;

let TRISECT_60_DEGREES = `!y. ~(constructible(vector[cos(pi / &9); y]))`;;
