(* ========================================================================= *)
(* #88: Formula for the number of derangements: round[n!/e]                  *)
(* ========================================================================= *)

needs "Library/transc.ml";;
needs "Library/calc_real.ml";;
needs "Library/floor.ml";;

let PAIR_BETA_THM = GEN_BETA_CONV `(\(x,y). P x y) (a,b)`;;

(* ------------------------------------------------------------------------- *)
(* Domain and range of a relation.                                           *)
(* ------------------------------------------------------------------------- *)

let domain = new_definition
 `domain r = {x | ?y. r(x,y)}`;;

let range = new_definition
 `range r = {y | ?x. r(x,y)}`;;

(* ------------------------------------------------------------------------- *)
(* Relational composition.                                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("%",(26, "right"));;

let compose = new_definition
 `(r % s) (x,y) <=> ?z. r(x,z) /\ s(z,y)`;;

(* ------------------------------------------------------------------------- *)
(* Identity relation on a domain.                                            *)
(* ------------------------------------------------------------------------- *)

let id = new_definition
 `id(s) (x,y) <=> x IN s /\ x = y`;;

(* ------------------------------------------------------------------------- *)
(* Converse relation.                                                        *)
(* ------------------------------------------------------------------------- *)

let converse = new_definition
 `converse(r) (x,y) = r(y,x)`;;

(* ------------------------------------------------------------------------- *)
(* Transposition.                                                            *)
(* ------------------------------------------------------------------------- *)

let swap = new_definition
 `swap(a,b) (x,y) <=> x = a /\ y = b \/ x = b /\ y = a`;;

(* ------------------------------------------------------------------------- *)
(* When a relation "pairs up" two sets bijectively.                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("pairsup",(12,"right"));;

let pairsup = new_definition
 `r pairsup (s,t) <=> (r % converse(r) = id(s)) /\ (converse(r) % r = id(t))`;;

(* ------------------------------------------------------------------------- *)
(* Special case of a permutation.                                            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("permutes",(12,"right"));;

let permutes = new_definition
 `r permutes s <=> r pairsup (s,s)`;;

(* ------------------------------------------------------------------------- *)
(* Even more special case of derangement.                                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("deranges",(12,"right"));;

let deranges = new_definition
 `r deranges s <=> r permutes s /\ !x. ~(r(x,x))`;;

(* ------------------------------------------------------------------------- *)
(* Trivial tactic for properties of relations.                               *)
(* ------------------------------------------------------------------------- *)

let REL_TAC =
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; EXISTS_PAIR_THM; PAIR_BETA_THM;
              permutes; pairsup; domain; range; compose; id; converse; swap;
              deranges; IN_INSERT; IN_DELETE; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  REWRITE_TAC[IN; EMPTY; INSERT; DELETE; UNION; IN_ELIM_THM; PAIR_EQ;
              id; converse; swap] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  ASM_MESON_TAC[];;

let REL_RULE tm = prove(tm,REL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some general properties of relations.                                     *)
(* ------------------------------------------------------------------------- *)

let CONVERSE_COMPOSE = `!r s. converse(r % s) = converse(s) % converse(r)`;;

let CONVERSE_CONVERSE = `!r. converse(converse r) = r`;;

(* ------------------------------------------------------------------------- *)
(* More "explicit" definition of pairing and permutation.                    *)
(* ------------------------------------------------------------------------- *)

let PAIRSUP_EXPLICIT = `!p s t.
        p pairsup (s,t) <=>
        (!x y. p(x,y) ==> x IN s /\ y IN t) /\
        (!x. x IN s ==> ?!y. y IN t /\ p(x,y)) /\
        (!y. y IN t ==> ?!x. x IN s /\ p(x,y))`;;

let PERMUTES_EXPLICIT = `!p s. p permutes s <=>
         (!x y. p(x,y) ==> x IN s /\ y IN s) /\
         (!x. x IN s ==> ?!y. y IN s /\ p(x,y)) /\
         (!y. y IN s ==> ?!x. x IN s /\ p(x,y))`;;

(* ------------------------------------------------------------------------- *)
(* Other low-level properties.                                               *)
(* ------------------------------------------------------------------------- *)

let PAIRSUP_DOMRAN = `!p s t. p pairsup (s,t) ==> domain p = s /\ range p = t`;;

let PERMUTES_DOMRAN = `!p s. p permutes s ==> domain p = s /\ range p = s`;;

let PAIRSUP_FUNCTIONAL = `!p s t. p pairsup (s,t) ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y'`;;

let PERMUTES_FUNCTIONAL = `!p s. p permutes s ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y'`;;

let PAIRSUP_COFUNCTIONAL = `!p s t. p pairsup (s,t) ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x'`;;

let PERMUTES_COFUNCTIONAL = `!p s. p permutes s ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x'`;;

(* ------------------------------------------------------------------------- *)
(* Some more abstract properties.                                            *)
(* ------------------------------------------------------------------------- *)

let PAIRSUP_ID = `!s. id(s) pairsup (s,s)`;;

let PERMUTES_ID = `!s. id(s) permutes s`;;

let PAIRSUP_CONVERSE = `!p s t. p pairsup (s,t) ==> converse(p) pairsup (t,s)`;;

let PERMUTES_CONVERSE = `!p s. p permutes s ==> converse(p) permutes s`;;

let PAIRSUP_COMPOSE = `!p p' s t u. p pairsup (s,t) /\ p' pairsup (t,u) ==> (p % p') pairsup (s,u)`;;

let PERMUTES_COMPOSE = `!p p' s. p permutes s /\ p' permutes s ==> (p % p') permutes s`;;

(* ------------------------------------------------------------------------- *)
(* Transpositions are permutations.                                          *)
(* ------------------------------------------------------------------------- *)

let PERMUTES_SWAP = `swap(a,b) permutes {a,b}`;;

(* ------------------------------------------------------------------------- *)
(* Clausal theorems for cases on first set.                                  *)
(* ------------------------------------------------------------------------- *)

let PAIRSUP_EMPTY = `p pairsup ({},{}) <=> (p = {})`;;

let PAIRSUP_INSERT = `!x:A s t:B->bool p.
        p pairsup (x INSERT s,t) <=>
          if x IN s then p pairsup (s,t)
          else ?y q. y IN t /\ p = (x,y) INSERT q /\ q pairsup (s,t DELETE y)`;;

(* ------------------------------------------------------------------------- *)
(* Number of pairings and permutations.                                      *)
(* ------------------------------------------------------------------------- *)

let NUMBER_OF_PAIRINGS = `!n s:A->bool t:B->bool.
        s HAS_SIZE n /\ t HAS_SIZE n
        ==> {p | p pairsup (s,t)} HAS_SIZE (FACT n)`;;

let NUMBER_OF_PERMUTATIONS = `!s n. s HAS_SIZE n ==> {p | p permutes s} HAS_SIZE (FACT n)`;;

(* ------------------------------------------------------------------------- *)
(* Number of derangements (we need to justify this later).                   *)
(* ------------------------------------------------------------------------- *)

let derangements = define
 `(derangements 0 = 1) /\
  (derangements 1 = 0) /\
  (derangements(n + 2) = (n + 1) * (derangements n + derangements(n + 1)))`;;

let DERANGEMENT_INDUCT = `!P. P 0 /\ P 1 /\ (!n. P n /\ P(n + 1) ==> P(n + 2)) ==> !n. P n`;;

(* ------------------------------------------------------------------------- *)
(* Expanding a derangement.                                                  *)
(* ------------------------------------------------------------------------- *)

let DERANGEMENT_ADD2 = `!p s x y.
        p deranges s /\ ~(x IN s) /\ ~(y IN s) /\ ~(x = y)
        ==> ((x,y) INSERT (y,x) INSERT p) deranges (x INSERT y INSERT s)`;;

let DERANGEMENT_ADD1 = `!p s y x. p deranges s /\ ~(y IN s) /\ p(x,z)
             ==> ((x,y) INSERT (y,z) INSERT (p DELETE (x,z)))
                 deranges (y INSERT s)`;;

(* ------------------------------------------------------------------------- *)
(* Number of derangements.                                                   *)
(* ------------------------------------------------------------------------- *)

let DERANGEMENT_EMPTY = `!p. p deranges {} <=> p = {}`;;

let DERANGEMENT_SING = `!x p. ~(p deranges {x})`;;

let NUMBER_OF_DERANGEMENTS = `!n s:A->bool. s HAS_SIZE n ==> {p | p deranges s} HAS_SIZE (derangements n)`;;

(* ------------------------------------------------------------------------- *)
(* Trivia.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SUM_1 = `sum(0..1) f = f 0 + f 1`;;

let SUM_2 = `sum(0..2) f = f 0 + f 1 + f 2`;;

(* ------------------------------------------------------------------------- *)
(* The key result.                                                           *)
(* ------------------------------------------------------------------------- *)

let DERANGEMENTS = `!n. ~(n = 0)
       ==> &(derangements n) =
           &(FACT n) * sum(0..n) (\k. --(&1) pow k / &(FACT k))`;;

(* ------------------------------------------------------------------------- *)
(* A more "explicit" formula. We could sharpen 1/2 to 0.3678794+epsilon      *)
(* ------------------------------------------------------------------------- *)

let DERANGEMENTS_EXP = `!n. ~(n = 0)
       ==> let e = exp(&1) in
           abs(&(derangements n) - &(FACT n) / e) < &1 / &2`;;

(* ------------------------------------------------------------------------- *)
(* Hence the critical "rounding" property.                                   *)
(* ------------------------------------------------------------------------- *)

let round = new_definition
 `round x = @n. integer(n) /\ n - &1 / &2 <= x /\ x < n + &1 / &2`;;

let ROUND_WORKS = `!x. integer(round x) /\ round x - &1 / &2 <= x /\ x < round x + &1 / &2`;;

let DERANGEMENTS_EXP = `!n. ~(n = 0)
       ==> let e = exp(&1) in &(derangements n) = round(&(FACT n) / e)`;;

(* ------------------------------------------------------------------------- *)
(* Put them together.                                                        *)
(* ------------------------------------------------------------------------- *)

let THE_DERANGEMENTS_FORMULA = `!n s. s HAS_SIZE n /\ ~(n = 0)
         ==> FINITE {p | p deranges s} /\
             let e = exp(&1) in
             &(CARD {p | p deranges s}) = round(&(FACT n) / e)`;;
