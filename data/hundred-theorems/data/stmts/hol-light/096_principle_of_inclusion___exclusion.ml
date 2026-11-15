(* ========================================================================= *)
(* Inclusion-exclusion principle, the usual and generalized forms.           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Simple set theory lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let SUBSET_INSERT_EXISTS = `!s x:A t. s SUBSET (x INSERT t) <=>
                s SUBSET t \/ ?u. u SUBSET t /\ s = x INSERT u`;;

let FINITE_SUBSETS_RESTRICT = `!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}`;;

(* ------------------------------------------------------------------------- *)
(* Versions for additive real functions, where the additivity applies only   *)
(* to some specific subsets (e.g. cardinality of finite sets, measurable     *)
(* sets with bounded measure).                                               *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED = `!P (f:(A->bool)->real) (A:I->bool) (x:I->(A->bool)).
        (!s t. P s /\ P t /\ DISJOINT s t
               ==> f(s UNION t) = f(s) + f(t)) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(x a))
        ==> f(UNIONS(IMAGE x A)) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS(IMAGE x B)))`;;

let INCLUSION_EXCLUSION_REAL_RESTRICTED = `!P (f:(A->bool)->real) (A:(A->bool)->bool).
        (!s t. P s /\ P t /\ DISJOINT s t
               ==> f(s UNION t) = f(s) + f(t)) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(a))
        ==> f(UNIONS A) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS B))`;;

(* ------------------------------------------------------------------------- *)
(* Versions for unrestrictedly additive functions.                           *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_REAL_INDEXED = `!(f:(A->bool)->real) (A:I->bool) (x:I->(A->bool)).
        (!s t. DISJOINT s t ==> f(s UNION t) = f(s) + f(t)) /\ FINITE A
        ==> f(UNIONS(IMAGE x A)) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS(IMAGE x B)))`;;

let INCLUSION_EXCLUSION_REAL = `!(f:(A->bool)->real) (A:(A->bool)->bool).
        (!s t. DISJOINT s t ==> f(s UNION t) = f(s) + f(t)) /\ FINITE A
        ==> f(UNIONS A) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS B))`;;

(* ------------------------------------------------------------------------- *)
(* Special case of cardinality, the most common case.                        *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION = `!s:(A->bool)->bool.
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> &(CARD(UNIONS s)) =
                sum {t | t SUBSET s /\ ~(t = {})}
                    (\t. (-- &1) pow (CARD t + 1) * &(CARD(INTERS t)))`;;

(* ------------------------------------------------------------------------- *)
(* A more conventional form.                                                 *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_USUAL = `!s:(A->bool)->bool.
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> &(CARD(UNIONS s)) =
                sum (1..CARD s) (\n. (-- &1) pow (n + 1) *
                                     sum {t | t SUBSET s /\ t HAS_SIZE n}
                                         (\t. &(CARD(INTERS t))))`;;

(* ------------------------------------------------------------------------- *)
(* A combinatorial lemma about subsets of a finite set.                      *)
(* ------------------------------------------------------------------------- *)

let FINITE_SUBSETS_RESTRICT = `!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}`;;

let CARD_ADJUST_LEMMA = `!f:A->B s x y.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        x = y + CARD (IMAGE f s)
        ==> x = y + CARD s`;;

let CARD_SUBSETS_STEP = `!x:A s. FINITE s /\ ~(x IN s) /\ u SUBSET s
           ==> CARD {t | t SUBSET (x INSERT s) /\ u SUBSET t /\ ODD(CARD t)} =
                 CARD {t | t SUBSET s /\ u SUBSET t /\ ODD(CARD t)} +
                 CARD {t | t SUBSET s /\ u SUBSET t /\ EVEN(CARD t)} /\
               CARD {t | t SUBSET (x INSERT s) /\ u SUBSET t /\ EVEN(CARD t)} =
                 CARD {t | t SUBSET s /\ u SUBSET t /\ EVEN(CARD t)} +
                 CARD {t | t SUBSET s /\ u SUBSET t /\ ODD(CARD t)}`;;

let CARD_SUBSUPERSETS_EVEN_ODD = `!s u:A->bool.
        FINITE u /\ s PSUBSET u
        ==> CARD {t | s SUBSET t /\ t SUBSET u /\ EVEN(CARD t)} =
            CARD {t | s SUBSET t /\ t SUBSET u /\ ODD(CARD t)}`;;

let SUM_ALTERNATING_CANCELS = `!s:A->bool f.
        FINITE s /\
        CARD {x | x IN s /\ EVEN(f x)} = CARD {x | x IN s /\ ODD(f x)}
        ==> sum s (\x. (-- &1) pow (f x)) = &0`;;

(* ------------------------------------------------------------------------- *)
(* Hence a general "Moebius inversion" inclusion-exclusion principle.        *)
(* This "symmetric" form is from Ira Gessel: "Symmetric Inclusion-Exclusion" *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_SYMMETRIC = `!f g:(A->bool)->real.
    (!s. FINITE s
         ==> g(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * f(t)))
    ==> !s. FINITE s
            ==> f(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * g(t))`;;

(* ------------------------------------------------------------------------- *)
(* The more typical non-symmetric version.                                   *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_MOBIUS = `!f g:(A->bool)->real.
        (!s. FINITE s ==> g(s) = sum {t | t SUBSET s} f)
        ==> !s. FINITE s
                ==> f(s) = sum {t | t SUBSET s}
                               (\t. (-- &1) pow (CARD s - CARD t) * g(t))`;;

(* ------------------------------------------------------------------------- *)
(* A related principle for real functions.                                   *)
(* ------------------------------------------------------------------------- *)

(*** Not clear how useful this is

needs "Library/products.ml";;

let INCLUSION_EXCLUSION_REAL_FUNCTION = `!f s:A->bool.
        FINITE s
        ==> product s (\x. &1 - f x) =
            sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * product t f)`;;

***)
