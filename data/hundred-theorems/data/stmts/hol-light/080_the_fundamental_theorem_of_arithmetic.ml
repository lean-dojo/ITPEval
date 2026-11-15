(* ========================================================================= *)
(* The fundamental theorem of arithmetic (unique prime factorization).       *)
(* ========================================================================= *)

needs "Library/prime.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Definition of iterated product.                                           *)
(* ------------------------------------------------------------------------- *)

let nproduct = new_definition `nproduct = iterate ( * )`;;

let NPRODUCT_CLAUSES = `(!f. nproduct {} f = 1) /\
   (!x f s. FINITE(s)
            ==> (nproduct (x INSERT s) f =
                 if x IN s then nproduct s f else f(x) * nproduct s f))`;;

let NPRODUCT_EQ_1_EQ = `!s f. FINITE s ==> (nproduct s f = 1 <=> !x. x IN s ==> f(x) = 1)`;;

let NPRODUCT_SPLITOFF = `!x:A f s. FINITE s
             ==> nproduct s f =
                 (if x IN s then f(x) else 1) * nproduct (s DELETE x) f`;;

let NPRODUCT_SPLITOFF_HACK = `!x:A f s. nproduct s f =
             if FINITE s then
               (if x IN s then f(x) else 1) * nproduct (s DELETE x) f
             else nproduct s f`;;

let NPRODUCT_EQ = `!f g s. FINITE s /\ (!x. x IN s ==> f x = g x)
           ==> nproduct s f = nproduct s g`;;

let NPRODUCT_EQ_GEN = `!f g s t. FINITE s /\ s = t /\ (!x. x IN s ==> f x = g x)
             ==> nproduct s f = nproduct t g`;;

let PRIME_DIVIDES_NPRODUCT = `!p s f. prime p /\ FINITE s /\ p divides (nproduct s f)
           ==> ?x. x IN s /\ p divides (f x)`;;

let NPRODUCT_CANCEL_PRIME = `!s p m f j.
        p EXP j * nproduct (s DELETE p) (\p. p EXP (f p)) = p * m
        ==> prime p /\ FINITE s /\ (!x. x IN s ==> prime x)
            ==> ~(j = 0) /\
                p EXP (j - 1) * nproduct (s DELETE p) (\p. p EXP (f p)) = m`;;

(* ------------------------------------------------------------------------- *)
(* Fundamental Theorem of Arithmetic.                                        *)
(* ------------------------------------------------------------------------- *)

let FTA = `!n. ~(n = 0)
       ==> ?!i. FINITE {p | ~(i p = 0)} /\
                (!p. ~(i p = 0) ==> prime p) /\
                n = nproduct {p | ~(i p = 0)} (\p. p EXP (i p))`;;
