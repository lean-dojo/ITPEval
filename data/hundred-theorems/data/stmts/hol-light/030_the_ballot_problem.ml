(* ========================================================================= *)
(* Ballot problem.                                                           *)
(* ========================================================================= *)

needs "Library/binomial.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Restricted function space.                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->",(13,"right"));;

let funspace = new_definition
 `(s --> t) = {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                        (!x. ~(x IN s) ==> f(x) = @y. T)}`;;

let FUNSPACE_EMPTY = `({} --> t) = {(\x. @y. T)}`;;

let HAS_SIZE_FUNSPACE = `!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s --> t) HAS_SIZE (n EXP m)`;;

let FINITE_FUNSPACE = `!s t. FINITE s /\ FINITE t ==> FINITE(s --> t)`;;

(* ------------------------------------------------------------------------- *)
(* Definition of the problem.                                                *)
(* ------------------------------------------------------------------------- *)

let vote_INDUCT,vote_RECURSION = define_type
 "vote = A | B";;

let all_countings = new_definition
 `all_countings a b =
        let n = a + b in
        CARD {f | f IN (1..n --> {A,B}) /\
                  CARD { i | i IN 1..n /\ f(i) = A} = a /\
                  CARD { i | i IN 1..n /\ f(i) = B} = b}`;;

let valid_countings = new_definition
 `valid_countings a b =
        let n = a + b in
        CARD {f | f IN (1..n --> {A,B}) /\
                  CARD { i | i IN 1..n /\ f(i) = A} = a /\
                  CARD { i | i IN 1..n /\ f(i) = B} = b /\
                  !m. 1 <= m /\ m <= n
                      ==> CARD { i | i IN 1..m /\ f(i) = A} >
                          CARD { i | i IN 1..m /\ f(i) = B}}`;;

(* ------------------------------------------------------------------------- *)
(* Various lemmas.                                                           *)
(* ------------------------------------------------------------------------- *)

let vote_CASES = cases "vote"
and vote_DISTINCT = distinctness "vote";;

let FINITE_COUNTINGS = `FINITE {f | f IN (1..n --> {A,B}) /\ P f}`;;

let UNIV_VOTE = `(:vote) = {A,B}`;;

let ADD1_NOT_IN_NUMSEG = `!m n. ~((n + 1) IN m..n)`;;

let NUMSEG_1_CLAUSES = `!n. 1..(n+1) = (n + 1) INSERT (1..n)`;;

let NUMSEG_RESTRICT_SUC = `{i | i IN 1..(n+1) /\ P i} =
        if P(n + 1) then (n + 1) INSERT {i | i IN 1..n /\ P i}
        else {i | i IN 1..n /\ P i}`;;

let CARD_NUMSEG_RESTRICT_SUC = `CARD {i | i IN 1..(n+1) /\ P i} =
        if P(n + 1) then CARD {i | i IN 1..n /\ P i} + 1
        else CARD {i | i IN 1..n /\ P i}`;;

let FORALL_RANGE_SUC = `(!i. 1 <= i /\ i <= n + 1 ==> P i) <=>
      P(n + 1) /\ (!i. 1 <= i /\ i <= n ==> P i)`;;

let IN_NUMSEG_RESTRICT_FALSE = `m <= n
   ==> (i IN 1..m /\ (if i = n + 1 then p i else q i) <=> i IN 1..m /\ q i)`;;

let CARD_NUMSEG_RESTRICT_EXTREMA = `(CARD {i | i IN 1..n /\ P i} = n <=> !i. 1 <= i /\ i <= n ==> P i) /\
   (CARD {i | i IN 1..n /\ P i} = 0 <=> !i. 1 <= i /\ i <= n ==> ~(P i))`;;

let VOTE_NOT_EQ = `(!x. ~(x = A) <=> x = B) /\
   (!x. ~(x = B) <=> x = A)`;;

let FUNSPACE_FIXED = `{f | f IN (s --> t) /\ (!i. i IN s ==> f i = a)} =
   if s = {} \/ a IN t then {(\i. if i IN s then a else @x. T)} else {}`;;

let COUNTING_LEMMA = `CARD {f | f IN (1..(n+1) --> {A,B}) /\ P f} =
   CARD {f | f IN (1..n --> {A,B}) /\ P (\i. if i = n + 1 then A else f i)} +
   CARD {f | f IN (1..n --> {A,B}) /\ P (\i. if i = n + 1 then B else f i)}`;;

(* ------------------------------------------------------------------------- *)
(* Recurrence relations.                                                     *)
(* ------------------------------------------------------------------------- *)

let ALL_COUNTINGS_0 = `!a. all_countings a 0 = 1 /\ all_countings 0 a = 1`;;

let VALID_COUNTINGS_0 = `valid_countings 0 0 = 1 /\
   !a. valid_countings (SUC a) 0 = 1 /\ valid_countings 0 (SUC a) = 0`;;

let ALL_COUNTINGS_SUC = `!a b. all_countings (a + 1) (b + 1) =
                all_countings a (b + 1) + all_countings (a + 1) b`;;

let VALID_COUNTINGS_SUC = `!a b. valid_countings (a + 1) (b + 1) =
                if a <= b then 0
                else valid_countings a (b + 1) + valid_countings (a + 1) b`;;

(* ------------------------------------------------------------------------- *)
(* Main result.                                                              *)
(* ------------------------------------------------------------------------- *)

let ALL_COUNTINGS = `!a b. all_countings a b = binom(a + b,a)`;;

let VALID_COUNTINGS = `!a b. (a + b) * valid_countings a b = (a - b) * binom(a + b,a)`;;

let BALLOT = `!a b. &(valid_countings a b) =
            if a <= b then if b = 0 then &1 else &0
            else (&a - &b) / (&a + &b) *  &(all_countings a b)`;;
