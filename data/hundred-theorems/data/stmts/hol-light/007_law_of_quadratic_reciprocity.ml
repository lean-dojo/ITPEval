(* ========================================================================= *)
(* Quadratic reciprocity.                                                    *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/pocklington.ml";;
needs "Library/products.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Misc. lemmas.                                                             *)
(* ------------------------------------------------------------------------- *)

let IN_NUMSEG_1 = `!p i. i IN 1..p - 1 <=> 0 < i /\ i < p`;;

let EVEN_DIV = `!n. EVEN n <=> n = 2 * (n DIV 2)`;;

let CONG_MINUS1_SQUARE = `2 <= p ==> ((p - 1) * (p - 1) == 1) (mod p)`;;

let CONG_EXP_MINUS1 = `!p n. 2 <= p ==> ((p - 1) EXP n == if EVEN n then 1 else p - 1) (mod p)`;;

let NOT_CONG_MINUS1 = `!p. 3 <= p ==> ~(p - 1 == 1) (mod p)`;;

let CONG_COND_LEMMA = `!p x y. 3 <= p /\
           ((if x then 1 else p - 1) == (if y then 1 else p - 1)) (mod p)
           ==> (x <=> y)`;;

let FINITE_SUBCROSS = `!s:A->bool t:B->bool.
       FINITE s /\ FINITE t ==> FINITE {x,y | x IN s /\ y IN t /\ P x y}`;;

let CARD_SUBCROSS_DETERMINATE = `FINITE s /\ FINITE t /\ (!x. x IN s /\ p(x) ==> f(x) IN t)
   ==> CARD {(x:A),(y:B) | x IN s /\ y IN t /\ y = f x /\ p x} =
       CARD {x | x IN s /\ p(x)}`;;

let CARD_SUBCROSS_SWAP = `CARD {y,x | y IN 1..m /\ x IN 1..n /\ P x y} =
   CARD {x,y | x IN 1..n /\ y IN 1..m /\ P x y}`;;

(* ------------------------------------------------------------------------- *)
(* What it means to be a quadratic residue. I keep in the "mod p" as what    *)
(* I think is a more intuitive notation.                                     *)
(*                                                                           *)
(* We might explicitly assume that the two numbers are coprime, ruling out   *)
(* the degenerate case of 0 as a quadratic residue. But this seems simpler.  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("is_quadratic_residue",(12,"right"));;

let is_quadratic_residue = new_definition
 `y is_quadratic_residue rel <=> ?x. (x EXP 2 == y) (rel)`;;

(* ------------------------------------------------------------------------- *)
(* Alternative formulation for special cases.                                *)
(* ------------------------------------------------------------------------- *)

let IS_QUADRATIC_RESIDUE = `!a p. ~(p = 0) /\ ~(p divides a)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p))`;;

let IS_QUADRATIC_RESIDUE_COMMON = `!a p. prime p /\ coprime(a,p)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p))`;;

(* ------------------------------------------------------------------------- *)
(* Some lemmas about dual pairs; these would be more natural over Z.         *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_RESIDUE_PAIR_ADD = `!p x y. prime p
           ==> (((x + y) EXP 2 == x EXP 2) (mod p) <=>
                 p divides y \/ p divides (2 * x + y))`;;

let QUADRATIC_RESIDUE_PAIR = `!p x y. prime p
           ==> ((x EXP 2 == y EXP 2) (mod p) <=>
                 p divides (x + y) \/ p divides (dist(x,y)))`;;

let IS_QUADRATIC_RESIDUE_PAIR = `!a p. prime p /\ coprime(a,p)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x y. 0 < x /\ x < p /\ 0 < y /\ y < p /\ x + y = p /\
                       (x EXP 2 == a) (mod p) /\ (y EXP 2 == a) (mod p) /\
                       !z. 0 < z /\ z < p /\ (z EXP 2 == a) (mod p)
                           ==> z = x \/ z = y)`;;

let QUADRATIC_RESIDUE_PAIR_PRODUCT = `!p x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p)
         ==> (x * (p - x) == (p - 1) * a) (mod p)`;;

(* ------------------------------------------------------------------------- *)
(* Define the Legendre symbol.                                               *)
(* ------------------------------------------------------------------------- *)

let legendre = new_definition
 `(legendre:num#num->int)(a,p) =
        if ~(coprime(a,p)) then &0
        else if a is_quadratic_residue (mod p) then &1
        else --(&1)`;;

(* ------------------------------------------------------------------------- *)
(* Definition of iterated product.                                           *)
(* ------------------------------------------------------------------------- *)

let nproduct = new_definition `nproduct = iterate ( * )`;;

let CONG_NPRODUCT = `!f g s. FINITE s /\ (!x. x IN s ==> (f x == g x) (mod n))
           ==> (nproduct s f == nproduct s g) (mod n)`;;

let NPRODUCT_DELTA_CONST = `!c s. FINITE s
         ==> nproduct s (\x. if p(x) then c else 1) =
             c EXP (CARD {x | x IN s /\ p(x)})`;;

let COPRIME_NPRODUCT = `!f p s. FINITE s /\ (!x. x IN s ==> coprime(p,f x))
           ==> coprime(p,nproduct s f)`;;

(* ------------------------------------------------------------------------- *)
(* Factorial in terms of products.                                           *)
(* ------------------------------------------------------------------------- *)

let FACT_NPRODUCT = `!n. FACT(n) = nproduct(1..n) (\i. i)`;;

(* ------------------------------------------------------------------------- *)
(* General "pairing up" theorem for products.                                *)
(* ------------------------------------------------------------------------- *)

let NPRODUCT_PAIRUP_INDUCT = `!f r n s k. s HAS_SIZE (2 * n) /\
               (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                      (f(x) * f(y) == k) (mod r))
               ==> (nproduct s f == k EXP n) (mod r)`;;

(* ------------------------------------------------------------------------- *)
(* The two cases.                                                            *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_NONRESIDUE_FACT = `!a p. prime p /\ ODD(p) /\
         coprime(a,p) /\ ~(a is_quadratic_residue (mod p))
         ==> (a EXP ((p - 1) DIV 2) == FACT(p - 1)) (mod p)`;;

let QUADRATIC_RESIDUE_FACT = `!a p. prime p /\ ODD(p) /\
         coprime(a,p) /\ a is_quadratic_residue (mod p)
         ==> (a EXP ((p - 1) DIV 2) == FACT(p - 2)) (mod p)`;;

(* ------------------------------------------------------------------------- *)
(* We immediately get one part of Wilson's theorem.                          *)
(* ------------------------------------------------------------------------- *)

let WILSON_LEMMA = `!p. prime(p) ==> (FACT(p - 2) == 1) (mod p)`;;

let WILSON_IMP = `!p. prime(p) ==> (FACT(p - 1) == p - 1) (mod p)`;;

let WILSON = `!p. ~(p = 1) ==> (prime p <=> (FACT(p - 1) == p - 1) (mod p))`;;

(* ------------------------------------------------------------------------- *)
(* Using Wilson's theorem we can get the Euler criterion.                    *)
(* ------------------------------------------------------------------------- *)

let EULER_CRITERION = `!a p. prime p /\ coprime(a,p)
         ==> (a EXP ((p - 1) DIV 2) ==
              (if a is_quadratic_residue (mod p) then 1 else p - 1)) (mod p)`;;

(* ------------------------------------------------------------------------- *)
(* Gauss's Lemma.                                                            *)
(* ------------------------------------------------------------------------- *)

let GAUSS_LEMMA_1 = `prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> nproduct(1..r) (\x. let b = (a * x) MOD p in
                           if b <= r then b else p - b) =
       nproduct(1..r) (\x. x)`;;

let GAUSS_LEMMA_2 = `prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> (nproduct(1..r) (\x. let b = (a * x) MOD p in
                            if b <= r then b else p - b) ==
        (p - 1) EXP (CARD {x | x IN 1..r /\ r < (a * x) MOD p}) *
        a EXP r * nproduct(1..r) (\x. x)) (mod p)`;;

let GAUSS_LEMMA_3 = `prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> ((p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} *
        (if a is_quadratic_residue mod p then 1 else p - 1) == 1) (mod p)`;;

let GAUSS_LEMMA_4 = `prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> ((if EVEN(CARD{x | x IN 1..r /\ r < (a * x) MOD p}) then 1 else p - 1) *
        (if a is_quadratic_residue mod p then 1 else p - 1) == 1) (mod p)`;;

let GAUSS_LEMMA = `!a p r. prime p /\ coprime(a,p) /\ 2 * r + 1 = p
           ==> (a is_quadratic_residue (mod p) <=>
                EVEN(CARD {x | x IN 1..r /\ r < (a * x) MOD p}))`;;

(* ------------------------------------------------------------------------- *)
(* A more symmetrical version.                                               *)
(* ------------------------------------------------------------------------- *)

let GAUSS_LEMMA_SYM = `!p q r s. prime p /\ prime q /\ coprime(p,q) /\
             2 * r + 1 = p /\ 2 * s + 1 = q
             ==> (q is_quadratic_residue (mod p) <=>
                  EVEN(CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                   q * x < p * y /\ p * y <= q * x + r}))`;;

let GAUSS_LEMMA_SYM' = `!p q r s. prime p /\ prime q /\ coprime(p,q) /\
             2 * r + 1 = p /\ 2 * s + 1 = q
             ==> (p is_quadratic_residue (mod q) <=>
                  EVEN(CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                   p * y < q * x /\ q * x <= p * y + s}))`;;

(* ------------------------------------------------------------------------- *)
(* The main result.                                                          *)
(* ------------------------------------------------------------------------- *)

let RECIPROCITY_SET_LEMMA = `!a b c d r s.
        a UNION b UNION c UNION d = (1..r) CROSS (1..s) /\
        PAIRWISE DISJOINT [a;b;c;d] /\ CARD b = CARD c
        ==> ((EVEN(CARD a) <=> EVEN(CARD d)) <=> ~(ODD r /\ ODD s))`;;

let RECIPROCITY_SIMPLE = `!p q r s.
        prime p /\
        prime q /\
        coprime (p,q) /\
        2 * r + 1 = p /\
        2 * s + 1 = q
        ==> ((q is_quadratic_residue (mod p) <=>
              p is_quadratic_residue (mod q)) <=>
             ~(ODD r /\ ODD s))`;;

(* ------------------------------------------------------------------------- *)
(* In terms of the Legendre symbol.                                          *)
(* ------------------------------------------------------------------------- *)

let RECIPROCITY_LEGENDRE = `!p q. prime p /\ prime q /\ ODD p /\ ODD q /\ ~(p = q)
         ==> legendre(p,q) * legendre(q,p) =
             --(&1) pow ((p - 1) DIV 2 * (q - 1) DIV 2)`;;
