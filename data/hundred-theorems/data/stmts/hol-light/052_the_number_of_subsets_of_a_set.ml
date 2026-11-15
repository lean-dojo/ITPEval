(* ========================================================================= *)
(* Very basic set theory (using predicates as sets).                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2016                       *)
(*              (c) Copyright, Marco Maggesi 2012-2017                       *)
(*             (c) Copyright, Andrea Gabrielli 2012-2017                     *)
(* ========================================================================= *)

needs "int.ml";;

(* ------------------------------------------------------------------------- *)
(* Infix symbols for set operations.                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("IN",(11,"right"));;
parse_as_infix("SUBSET",(12,"right"));;
parse_as_infix("PSUBSET",(12,"right"));;
parse_as_infix("INTER",(20,"right"));;
parse_as_infix("UNION",(16,"right"));;
parse_as_infix("DIFF",(18,"left"));;
parse_as_infix("INSERT",(21,"right"));;
parse_as_infix("DELETE",(21,"left"));;

parse_as_infix("HAS_SIZE",(12,"right"));;
parse_as_infix("<=_c",(12,"right"));;
parse_as_infix("<_c",(12,"right"));;
parse_as_infix(">=_c",(12,"right"));;
parse_as_infix(">_c",(12,"right"));;
parse_as_infix("=_c",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(* Set membership.                                                           *)
(* ------------------------------------------------------------------------- *)

let IN = new_definition
  `!P:A->bool. !x. x IN P <=> P x`;;

(* ------------------------------------------------------------------------- *)
(* Axiom of extensionality in this framework.                                *)
(* ------------------------------------------------------------------------- *)

let EXTENSION = `!s t. (s = t) <=> !x:A. x IN s <=> x IN t`;;

(* ------------------------------------------------------------------------- *)
(* General specification.                                                    *)
(* ------------------------------------------------------------------------- *)

let GSPEC = new_definition
  `GSPEC (p:A->bool) = p`;;

let SETSPEC = new_definition
  `SETSPEC (v:A) P t <=> P /\ (v = t)`;;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for eliminating set-comprehension membership assertions.     *)
(* ------------------------------------------------------------------------- *)

let IN_ELIM_THM = `(!P x:A. x IN GSPEC (\v. P (SETSPEC v)) <=> P (\p t. p /\ (x = t))) /\
   (!p x:A. x IN GSPEC (\v. ?y. SETSPEC v (p y) y) <=> p x) /\
   (!P x:A. GSPEC (\v. P (SETSPEC v)) x <=> P (\p t. p /\ (x = t))) /\
   (!p x:A. GSPEC (\v. ?y. SETSPEC v (p y) y) x <=> p x) /\
   (!p x:A. x IN (\y. p y) <=> p x)`;;

(* ------------------------------------------------------------------------- *)
(* These two definitions are needed first, for the parsing of enumerations.  *)
(* ------------------------------------------------------------------------- *)

let EMPTY = new_definition
  `EMPTY = (\x:A. F)`;;

let INSERT_DEF = new_definition
  `x INSERT s = \y:A. y IN s \/ (y = x)`;;

(* ------------------------------------------------------------------------- *)
(* The other basic operations.                                               *)
(* ------------------------------------------------------------------------- *)

let UNIV = new_definition
  `UNIV = (\x:A. T)`;;

let UNION = new_definition
  `s UNION t = {x:A | x IN s \/ x IN t}`;;

let UNIONS = new_definition
  `UNIONS s = {x:A | ?u. u IN s /\ x IN u}`;;

let INTER = new_definition
  `s INTER t = {x:A | x IN s /\ x IN t}`;;

let INTERS = new_definition
  `INTERS s = {x:A | !u. u IN s ==> x IN u}`;;

let DIFF = new_definition
  `s DIFF t =  {x:A | x IN s /\ ~(x IN t)}`;;

let INSERT = `x INSERT s = {y:A | y IN s \/ (y = x)}`;;

let DELETE = new_definition
  `s DELETE x = {y:A | y IN s /\ ~(y = x)}`;;

(* ------------------------------------------------------------------------- *)
(* Other basic predicates.                                                   *)
(* ------------------------------------------------------------------------- *)

let SUBSET = new_definition
  `s SUBSET t <=> !x:A. x IN s ==> x IN t`;;

let PSUBSET = new_definition
  `(s:A->bool) PSUBSET t <=> s SUBSET t /\ ~(s = t)`;;

let DISJOINT = new_definition
  `DISJOINT (s:A->bool) t <=> (s INTER t = EMPTY)`;;

let SING = new_definition
  `SING s = ?x:A. s = {x}`;;

(* ------------------------------------------------------------------------- *)
(* Finiteness.                                                               *)
(* ------------------------------------------------------------------------- *)

let FINITE_RULES,FINITE_INDUCT,FINITE_CASES =
  new_inductive_definition
    `FINITE (EMPTY:A->bool) /\
     !(x:A) s. FINITE s ==> FINITE (x INSERT s)`;;

let INFINITE = new_definition
  `INFINITE (s:A->bool) <=> ~(FINITE s)`;;

(* ------------------------------------------------------------------------- *)
(* Stuff concerned with functions.                                           *)
(* ------------------------------------------------------------------------- *)

let IMAGE = new_definition
  `IMAGE (f:A->B) s = { y | ?x. x IN s /\ (y = f x)}`;;

let INJ = new_definition
  `INJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))`;;

let SURJ = new_definition
  `SURJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x. (x IN t) ==> ?y. y IN s /\ (f y = x))`;;

let BIJ = new_definition
  `BIJ (f:A->B) s t <=> INJ f s t /\ SURJ f s t`;;

(* ------------------------------------------------------------------------- *)
(* Another funny thing.                                                      *)
(* ------------------------------------------------------------------------- *)

let CHOICE = new_definition
  `CHOICE s = @x:A. x IN s`;;

let REST = new_definition
  `REST (s:A->bool) = s DELETE (CHOICE s)`;;

(* ------------------------------------------------------------------------- *)
(* Basic membership properties.                                              *)
(* ------------------------------------------------------------------------- *)

let NOT_IN_EMPTY = `!x:A. ~(x IN EMPTY)`;;

let IN_UNIV = `!x:A. x IN UNIV`;;

let IN_UNION = `!s t (x:A). x IN (s UNION t) <=> x IN s \/ x IN t`;;

let IN_UNIONS = `!s (x:A). x IN (UNIONS s) <=> ?t. t IN s /\ x IN t`;;

let IN_INTER = `!s t (x:A). x IN (s INTER t) <=> x IN s /\ x IN t`;;

let IN_INTERS = `!s (x:A). x IN (INTERS s) <=> !t. t IN s ==> x IN t`;;

let IN_DIFF = `!(s:A->bool) t x. x IN (s DIFF t) <=> x IN s /\ ~(x IN t)`;;

let IN_INSERT = `!x:A. !y s. x IN (y INSERT s) <=> (x = y) \/ x IN s`;;

let IN_DELETE = `!s. !x:A. !y. x IN (s DELETE y) <=> x IN s /\ ~(x = y)`;;

let IN_SING = `!x y. x IN {y:A} <=> (x = y)`;;

let IN_IMAGE = `!y:B. !s f. (y IN (IMAGE f s)) <=> ?x:A. (y = f x) /\ x IN s`;;

let IN_REST = `!x:A. !s. x IN (REST s) <=> x IN s /\ ~(x = CHOICE s)`;;

let FORALL_IN_INSERT = `!P a s. (!x:A. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x)`;;

let EXISTS_IN_INSERT = `!P a s. (?x:A. x IN (a INSERT s) /\ P x) <=> P a \/ ?x. x IN s /\ P x`;;

let FORALL_IN_UNION = `!P s t:A->bool.
        (!x. x IN s UNION t ==> P x) <=>
        (!x. x IN s ==> P x) /\ (!x. x IN t ==> P x)`;;

let EXISTS_IN_UNION = `!P s t:A->bool.
        (?x. x IN s UNION t /\ P x) <=>
        (?x. x IN s /\ P x) \/ (?x. x IN t /\ P x)`;;

let FORALL_IN_IMAGE = `!(f:A->B) s. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))`;;

let EXISTS_IN_IMAGE = `!(f:A->B) s. (?y. y IN IMAGE f s /\ P y) <=> ?x. x IN s /\ P(f x)`;;

let FORALL_IN_GSPEC = `(!P Q (f:A->B). (!z. z IN {f x | P x} ==> Q z) <=> (!x. P x ==> Q(f x))) /\
   (!P Q (f:A->B->C).
        (!z. z IN {f x y | P x y} ==> Q z) <=>
        (!x y. P x y ==> Q(f x y))) /\
   (!P Q (f:A->B->C->D).
        (!z. z IN {f w x y | P w x y} ==> Q z) <=>
        (!w x y. P w x y ==> Q(f w x y))) /\
   (!P Q (f:A->B->C->D->E).
        (!z. z IN {f v w x y | P v w x y} ==> Q z) <=>
        (!v w x y. P v w x y ==> Q(f v w x y)))`;;

let EXISTS_IN_GSPEC = `(!P Q (f:A->B). (?z. z IN {f x | P x} /\ Q z) <=> (?x. P x /\ Q(f x))) /\
   (!P Q (f:A->B->C).
        (?z. z IN {f x y | P x y} /\ Q z) <=>
        (?x y. P x y /\ Q(f x y))) /\
   (!P Q (f:A->B->C->D).
        (?z. z IN {f w x y | P w x y} /\ Q z) <=>
        (?w x y. P w x y /\ Q(f w x y))) /\
   (!P Q (f:A->B->C->D->E).
        (?z. z IN {f v w x y | P v w x y} /\ Q z) <=>
        (?v w x y. P v w x y /\ Q(f v w x y)))`;;

let UNIONS_IMAGE = `!(f:A->B->bool) s. UNIONS (IMAGE f s) = {y | ?x. x IN s /\ y IN f x}`;;

let INTERS_IMAGE = `!(f:A->B->bool) s. INTERS (IMAGE f s) = {y | !x. x IN s ==> y IN f x}`;;

let UNIONS_GSPEC = `(!P (f:A->B->bool).
        UNIONS {f x | P x} = {a | ?x. P x /\ a IN (f x)}) /\
   (!P (f:A->B->C->bool).
        UNIONS {f x y | P x y} = {a | ?x y. P x y /\ a IN (f x y)}) /\
   (!P (f:A->B->C->D->bool).
        UNIONS {f x y z | P x y z} =
        {a | ?x y z. P x y z /\ a IN (f x y z)})`;;

let INTERS_GSPEC = `(!P (f:A->B->bool).
        INTERS {f x | P x} = {a | !x. P x ==> a IN (f x)}) /\
   (!P (f:A->B->C->bool).
        INTERS {f x y | P x y} = {a | !x y. P x y ==> a IN (f x y)}) /\
   (!P (f:A->B->C->D->bool).
        INTERS {f x y z | P x y z} =
        {a | !x y z. P x y z ==> a IN (f x y z)})`;;

(* ------------------------------------------------------------------------- *)
(* Basic property of the choice function.                                    *)
(* ------------------------------------------------------------------------- *)

let CHOICE_DEF = `!s:A->bool. ~(s = EMPTY) ==> (CHOICE s) IN s`;;

(* ------------------------------------------------------------------------- *)
(* Tactic to automate some routine set theory by reduction to FOL.           *)
(* ------------------------------------------------------------------------- *)

let SET_TAC =
  let PRESET_CONV =
    REWRITE_CONV[INTERS_IMAGE; INTERS_GSPEC; UNIONS_IMAGE; UNIONS_GSPEC] THENC
    REWRITE_CONV[EXTENSION; SUBSET; PSUBSET; DISJOINT; SING;
                 BIJ; INJ; SURJ] THENC
    REWRITE_CONV[NOT_IN_EMPTY; IN_UNIV; IN_UNION; IN_INTER; IN_DIFF; IN_INSERT;
                 IN_DELETE; IN_REST; IN_INTERS; IN_UNIONS; IN_IMAGE;
                 IN_ELIM_THM; IN] in
  fun ths ->
    MAP_EVERY MP_TAC ths THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(COND_CASES_TAC THEN POP_ASSUM MP_TAC) THEN
    CONV_TAC PRESET_CONV THEN MAP_EVERY MP_TAC
     (filter (fun th -> CONV_RULE PRESET_CONV th = TRUTH) ths) THEN
    REWRITE_TAC[IN] THEN MESON_TAC[];;

let SET_RULE tm = prove(tm,SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Misc. theorems.                                                           *)
(* ------------------------------------------------------------------------- *)

let NOT_EQUAL_SETS = `!s:A->bool. !t. ~(s = t) <=> ?x. x IN t <=> ~(x IN s)`;;

let INSERT_RESTRICT = `!P s a:A.
        {x | x IN a INSERT s /\ P x} =
        if P a then a INSERT {x | x IN s /\ P x} else {x | x IN s /\ P x}`;;

let UNIV_1 = `(:1) = {one}`;;

(* ------------------------------------------------------------------------- *)
(* The empty set.                                                            *)
(* ------------------------------------------------------------------------- *)

let MEMBER_NOT_EMPTY = `!s:A->bool. (?x. x IN s) <=> ~(s = EMPTY)`;;

(* ------------------------------------------------------------------------- *)
(* The universal set.                                                        *)
(* ------------------------------------------------------------------------- *)

let UNIV_NOT_EMPTY = `~(UNIV:A->bool = EMPTY)`;;

let EMPTY_NOT_UNIV = `~(EMPTY:A->bool = UNIV)`;;

let EQ_UNIV = `(!x:A. x IN s) <=> (s = UNIV)`;;

(* ------------------------------------------------------------------------- *)
(* Set inclusion.                                                            *)
(* ------------------------------------------------------------------------- *)

let SUBSET_TRANS = `!(s:A->bool) t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u`;;

let SUBSET_REFL = `!s:A->bool. s SUBSET s`;;

let SUBSET_ANTISYM = `!(s:A->bool) t. s SUBSET t /\ t SUBSET s ==> s = t`;;

let SUBSET_ANTISYM_EQ = `!(s:A->bool) t. s SUBSET t /\ t SUBSET s <=> s = t`;;

let EMPTY_SUBSET = `!s:A->bool. EMPTY SUBSET s`;;

let SUBSET_EMPTY = `!s:A->bool. s SUBSET EMPTY <=> (s = EMPTY)`;;

let SUBSET_UNIV = `!s:A->bool. s SUBSET UNIV`;;

let UNIV_SUBSET = `!s:A->bool. UNIV SUBSET s <=> (s = UNIV)`;;

let SING_SUBSET = `!s x:A. {x} SUBSET s <=> x IN s`;;

let SUBSET_RESTRICT = `!s P. {x:A | x IN s /\ P x} SUBSET s`;;

(* ------------------------------------------------------------------------- *)
(* Proper subset.                                                            *)
(* ------------------------------------------------------------------------- *)

let PSUBSET_TRANS = `!(s:A->bool) t u. s PSUBSET t /\ t PSUBSET u ==> s PSUBSET u`;;

let PSUBSET_SUBSET_TRANS = `!(s:A->bool) t u. s PSUBSET t /\ t SUBSET u ==> s PSUBSET u`;;

let SUBSET_PSUBSET_TRANS = `!(s:A->bool) t u. s SUBSET t /\ t PSUBSET u ==> s PSUBSET u`;;

let PSUBSET_IRREFL = `!s:A->bool. ~(s PSUBSET s)`;;

let NOT_PSUBSET_EMPTY = `!s:A->bool. ~(s PSUBSET EMPTY)`;;

let NOT_UNIV_PSUBSET = `!s:A->bool. ~(UNIV PSUBSET s)`;;

let PSUBSET_UNIV = `!s:A->bool. s PSUBSET UNIV <=> ?x. ~(x IN s)`;;

let PSUBSET_ALT = `!s t:A->bool. s PSUBSET t <=> s SUBSET t /\ (?a. a IN t /\ ~(a IN s))`;;

(* ------------------------------------------------------------------------- *)
(* Union.                                                                    *)
(* ------------------------------------------------------------------------- *)

let UNION_ASSOC = `!(s:A->bool) t u. (s UNION t) UNION u = s UNION (t UNION u)`;;

let UNION_IDEMPOT = `!s:A->bool. s UNION s = s`;;

let UNION_COMM = `!(s:A->bool) t. s UNION t = t UNION s`;;

let SUBSET_UNION = `(!s:A->bool. !t. s SUBSET (s UNION t)) /\
   (!s:A->bool. !t. s SUBSET (t UNION s))`;;

let SUBSET_UNION_ABSORPTION = `!s:A->bool. !t. s SUBSET t <=> (s UNION t = t)`;;

let UNION_EMPTY = `(!s:A->bool. EMPTY UNION s = s) /\
   (!s:A->bool. s UNION EMPTY = s)`;;

let UNION_UNIV = `(!s:A->bool. UNIV UNION s = UNIV) /\
   (!s:A->bool. s UNION UNIV = UNIV)`;;

let EMPTY_UNION = `!s:A->bool. !t. (s UNION t = EMPTY) <=> (s = EMPTY) /\ (t = EMPTY)`;;

let UNION_SUBSET = `!s t u:A->bool. (s UNION t) SUBSET u <=> s SUBSET u /\ t SUBSET u`;;

let UNION_RESTRICT = `!P s t:A->bool.
        {x | x IN (s UNION t) /\ P x} =
        {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`;;

let FORALL_SUBSET_UNION = `!t u:A->bool.
        (!s. s SUBSET t UNION u ==> P s) <=>
        (!t' u'. t' SUBSET t /\ u' SUBSET u ==> P(t' UNION u'))`;;

let EXISTS_SUBSET_UNION = `!t u:A->bool.
        (?s. s SUBSET t UNION u /\ P s) <=>
        (?t' u'. t' SUBSET t /\ u' SUBSET u /\ P(t' UNION u'))`;;

let FORALL_SUBSET_INSERT = `!a:A t. (!s. s SUBSET a INSERT t ==> P s) <=>
           (!s. s SUBSET t ==> P s /\ P (a INSERT s))`;;

let EXISTS_SUBSET_INSERT = `!a:A t. (?s. s SUBSET a INSERT t /\ P s) <=>
           (?s. s SUBSET t /\ (P s \/ P (a INSERT s)))`;;

(* ------------------------------------------------------------------------- *)
(* Intersection.                                                             *)
(* ------------------------------------------------------------------------- *)

let INTER_ASSOC = `!(s:A->bool) t u. (s INTER t) INTER u = s INTER (t INTER u)`;;

let INTER_IDEMPOT = `!s:A->bool. s INTER s = s`;;

let INTER_COMM = `!(s:A->bool) t. s INTER t = t INTER s`;;

let INTER_SUBSET = `(!s:A->bool. !t. (s INTER t) SUBSET s) /\
   (!s:A->bool. !t. (t INTER s) SUBSET s)`;;

let SUBSET_INTER_ABSORPTION = `!s:A->bool. !t. s SUBSET t <=> (s INTER t = s)`;;

let INTER_EMPTY = `(!s:A->bool. EMPTY INTER s = EMPTY) /\
   (!s:A->bool. s INTER EMPTY = EMPTY)`;;

let INTER_UNIV = `(!s:A->bool. UNIV INTER s = s) /\
   (!s:A->bool. s INTER UNIV = s)`;;

let SUBSET_INTER = `!s t u:A->bool. s SUBSET (t INTER u) <=> s SUBSET t /\ s SUBSET u`;;

let INTER_RESTRICT = `!P s (t:A->bool).
        {x | x IN (s INTER t) /\ P x} =
        {x | x IN s /\ P x} INTER {x | x IN t /\ P x}`;;

(* ------------------------------------------------------------------------- *)
(* Distributivity.                                                           *)
(* ------------------------------------------------------------------------- *)

let UNION_OVER_INTER = `!s:A->bool. !t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`;;

let INTER_OVER_UNION = `!s:A->bool. !t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)`;;

(* ------------------------------------------------------------------------- *)
(* Disjoint sets.                                                            *)
(* ------------------------------------------------------------------------- *)

let IN_DISJOINT = `!s:A->bool. !t. DISJOINT s t <=> ~(?x. x IN s /\ x IN t)`;;

let DISJOINT_SYM = `!s:A->bool. !t. DISJOINT s t <=> DISJOINT t s`;;

let DISJOINT_EMPTY = `!s:A->bool. DISJOINT EMPTY s /\ DISJOINT s EMPTY`;;

let DISJOINT_EMPTY_REFL = `!s:A->bool. (s = EMPTY) <=> (DISJOINT s s)`;;

let DISJOINT_UNION = `!s:A->bool. !t u. DISJOINT (s UNION t) u <=> DISJOINT s u /\ DISJOINT t u`;;

let DISJOINT_SING = `(!s a:A. DISJOINT s {a} <=> ~(a IN s)) /\
   (!s a:A. DISJOINT {a} s <=> ~(a IN s))`;;

(* ------------------------------------------------------------------------- *)
(* Set difference.                                                           *)
(* ------------------------------------------------------------------------- *)

let DIFF_EMPTY = `!s:A->bool. s DIFF EMPTY = s`;;

let EMPTY_DIFF = `!s:A->bool. EMPTY DIFF s = EMPTY`;;

let DIFF_UNIV = `!s:A->bool. s DIFF UNIV = EMPTY`;;

let DIFF_DIFF = `!s:A->bool. !t. (s DIFF t) DIFF t = s DIFF t`;;

let DIFF_EQ_EMPTY = `!s:A->bool. s DIFF s = EMPTY`;;

let SUBSET_DIFF = `!s t:A->bool. (s DIFF t) SUBSET s`;;

let COMPL_COMPL = `!s. (:A) DIFF ((:A) DIFF s) = s`;;

let DIFF_RESTRICT = `!P s (t:A->bool).
        {x | x IN (s DIFF t) /\ P x} =
        {x | x IN s /\ P x} DIFF {x | x IN t /\ P x}`;;

(* ------------------------------------------------------------------------- *)
(* Insertion and deletion.                                                   *)
(* ------------------------------------------------------------------------- *)

let COMPONENT = `!x:A. !s. x IN (x INSERT s)`;;

let DECOMPOSITION = `!s:A->bool. !x. x IN s <=> ?t. (s = x INSERT t) /\ ~(x IN t)`;;

let SET_CASES = `!s:A->bool. (s = EMPTY) \/ ?x:A. ?t. (s = x INSERT t) /\ ~(x IN t)`;;

let ABSORPTION = `!x:A. !s. x IN s <=> (x INSERT s = s)`;;

let INSERT_INSERT = `!x:A. !s. x INSERT (x INSERT s) = x INSERT s`;;

let INSERT_COMM = `!x:A. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)`;;

let INSERT_UNIV = `!x:A. x INSERT UNIV = UNIV`;;

let NOT_INSERT_EMPTY = `!x:A. !s. ~(x INSERT s = EMPTY)`;;

let NOT_EMPTY_INSERT = `!x:A. !s. ~(EMPTY = x INSERT s)`;;

let INSERT_UNION = `!x:A. !s t. (x INSERT s) UNION t =
               if x IN t then s UNION t else x INSERT (s UNION t)`;;

let INSERT_UNION_EQ = `!x:A. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)`;;

let INSERT_INTER = `!x:A. !s t. (x INSERT s) INTER t =
               if x IN t then x INSERT (s INTER t) else s INTER t`;;

let DISJOINT_INSERT = `!(x:A) s t. DISJOINT (x INSERT s) t <=> (DISJOINT s t) /\ ~(x IN t)`;;

let INSERT_SUBSET = `!x:A. !s t. (x INSERT s) SUBSET t <=> (x IN t /\ s SUBSET t)`;;

let SUBSET_INSERT = `!x:A. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) <=> s SUBSET t`;;

let INSERT_DIFF = `!s t. !x:A. (x INSERT s) DIFF t =
               if x IN t then s DIFF t else x INSERT (s DIFF t)`;;

let INSERT_AC = `(x:A) INSERT (y INSERT s) = y INSERT (x INSERT s) /\
   x INSERT (x INSERT s) = x INSERT s`;;

let INTER_ACI = `((p:A->bool) INTER q = q INTER p) /\
   ((p INTER q) INTER r = p INTER q INTER r) /\
   (p INTER q INTER r = q INTER p INTER r) /\
   (p INTER p = p) /\
   (p INTER p INTER q = p INTER q)`;;

let UNION_ACI = `((p:A->bool) UNION q = q UNION p) /\
   ((p UNION q) UNION r = p UNION q UNION r) /\
   (p UNION q UNION r = q UNION p UNION r) /\
   (p UNION p = p) /\
   (p UNION p UNION q = p UNION q)`;;

let DELETE_NON_ELEMENT = `!x:A. !s. ~(x IN s) <=> (s DELETE x = s)`;;

let IN_DELETE_EQ = `!s x. !x':A.
     (x IN s <=> x' IN s) <=> (x IN (s DELETE x') <=> x' IN (s DELETE x))`;;

let EMPTY_DELETE = `!x:A. EMPTY DELETE x = EMPTY`;;

let DELETE_DELETE = `!x:A. !s. (s DELETE x) DELETE x = s DELETE x`;;

let DELETE_COMM = `!x:A. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x`;;

let DELETE_SUBSET = `!x:A. !s. (s DELETE x) SUBSET s`;;

let SUBSET_DELETE = `!x:A. !s t. s SUBSET (t DELETE x) <=> ~(x IN s) /\ (s SUBSET t)`;;

let SUBSET_INSERT_DELETE = `!x:A. !s t. s SUBSET (x INSERT t) <=> ((s DELETE x) SUBSET t)`;;

let DIFF_INSERT = `!s t. !x:A. s DIFF (x INSERT t) = (s DELETE x) DIFF t`;;

let PSUBSET_INSERT_SUBSET = `!s t. s PSUBSET t <=> ?x:A. ~(x IN s) /\ (x INSERT s) SUBSET t`;;

let DELETE_INSERT = `!x:A. !y s.
      (x INSERT s) DELETE y =
        if x = y then s DELETE y else x INSERT (s DELETE y)`;;

let INSERT_DELETE = `!x:A. !s. x IN s ==> (x INSERT (s DELETE x) = s)`;;

let DELETE_INTER = `!s t. !x:A. (s DELETE x) INTER t = (s INTER t) DELETE x`;;

let DISJOINT_DELETE_SYM = `!s t. !x:A. DISJOINT (s DELETE x) t = DISJOINT (t DELETE x) s`;;

(* ------------------------------------------------------------------------- *)
(* Multiple union.                                                           *)
(* ------------------------------------------------------------------------- *)

let UNIONS_0 = `UNIONS {}:A->bool = {}`;;

let UNIONS_1 = `!s:A->bool. UNIONS {s} = s`;;

let UNIONS_2 = `!s (t:A->bool). UNIONS {s,t} = s UNION t`;;

let UNIONS_INSERT = `!(s:A->bool) u. UNIONS (s INSERT u) = s UNION (UNIONS u)`;;

let FORALL_IN_UNIONS = `!P s. (!x:A. x IN UNIONS s ==> P x) <=> !t x. t IN s /\ x IN t ==> P x`;;

let EXISTS_IN_UNIONS = `!P s. (?x:A. x IN UNIONS s /\ P x) <=> (?t x. t IN s /\ x IN t /\ P x)`;;

let EMPTY_UNIONS = `!s. (UNIONS s = {}) <=> !t:A->bool. t IN s ==> t = {}`;;

let INTER_UNIONS = `(!s (t:A->bool). UNIONS s INTER t = UNIONS {x INTER t | x IN s}) /\
   (!s (t:A->bool). t INTER UNIONS s = UNIONS {t INTER x | x IN s})`;;

let UNIONS_SUBSET = `!f (t:A->bool). UNIONS f SUBSET t <=> !s. s IN f ==> s SUBSET t`;;

let SUBSET_UNIONS = `!(f:(A->bool)->bool) g. f SUBSET g ==> UNIONS f SUBSET UNIONS g`;;

let UNIONS_UNION = `!s t:(A->bool)->bool. UNIONS(s UNION t) = (UNIONS s) UNION (UNIONS t)`;;

let INTERS_UNION = `!s t:(A->bool)->bool. INTERS (s UNION t) = INTERS s INTER INTERS t`;;

let UNIONS_MONO = `!s t:(A->bool)->bool.
    (!x. x IN s ==> ?y. y IN t /\ x SUBSET y) ==> UNIONS s SUBSET UNIONS t`;;

let UNIONS_MONO_IMAGE = `!(f:A->B->bool) g s.
        (!x. x IN s ==> f x SUBSET g x)
        ==> UNIONS(IMAGE f s) SUBSET UNIONS(IMAGE g s)`;;

let UNIONS_UNIV = `UNIONS (:A->bool) = (:A)`;;

let UNIONS_INSERT_EMPTY = `!s:(A->bool)->bool. UNIONS({} INSERT s) = UNIONS s`;;

let UNIONS_DELETE_EMPTY = `!s:(A->bool)->bool. UNIONS(s DELETE {}) = UNIONS s`;;

(* ------------------------------------------------------------------------- *)
(* Multiple intersection.                                                    *)
(* ------------------------------------------------------------------------- *)

let INTERS_0 = `INTERS {} = (:A)`;;

let INTERS_1 = `!s:A->bool. INTERS {s} = s`;;

let INTERS_2 = `!s (t:A->bool). INTERS {s,t} = s INTER t`;;

let INTERS_INSERT = `!(s:A->bool) u. INTERS (s INSERT u) = s INTER (INTERS u)`;;

let SUBSET_INTERS = `!(s:A->bool) f. s SUBSET INTERS f <=> (!t. t IN f ==> s SUBSET t)`;;

let INTERS_SUBSET = `!u s:A->bool.
    ~(u = {}) /\ (!t. t IN u ==> t SUBSET s) ==> INTERS u SUBSET s`;;

let INTERS_SUBSET_STRONG = `!u s:A->bool. (?t. t IN u /\ t SUBSET s) ==> INTERS u SUBSET s`;;

let INTERS_ANTIMONO = `!(f:(A->bool)->bool) g. g SUBSET f ==> INTERS f SUBSET INTERS g`;;

let INTERS_EQ_UNIV = `!f. INTERS f = (:A) <=> !s. s IN f ==> s = (:A)`;;

let INTERS_ANTIMONO_GEN = `!s (t:(A->bool)->bool).
        (!y. y IN t ==> ?x. x IN s /\ x SUBSET y)
        ==> INTERS s SUBSET INTERS t`;;

(* ------------------------------------------------------------------------- *)
(* Image.                                                                    *)
(* ------------------------------------------------------------------------- *)

let IMAGE_CLAUSES = `(IMAGE (f:A->B) {} = {}) /\
   (IMAGE f (x INSERT s) = (f x) INSERT (IMAGE f s))`;;

let IMAGE_UNION = `!(f:A->B) s t. IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t)`;;

let IMAGE_ID = `!s:A->bool. IMAGE (\x. x) s = s`;;

let IMAGE_I = `!s:A->bool. IMAGE I s = s`;;

let IMAGE_o = `!(f:B->C) (g:A->B) s. IMAGE (f o g) s = IMAGE f (IMAGE g s)`;;

let IMAGE_SUBSET = `!(f:A->B) s t. s SUBSET t ==> (IMAGE f s) SUBSET (IMAGE f t)`;;

let IMAGE_INTER_INJ = `!(f:A->B) s t.
        (!x y. f(x) = f(y) ==> x = y)
        ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t))`;;

let IMAGE_DIFF_INJ = `!f:A->B s t.
        (!x y. x IN s /\ y IN t /\ f x = f y ==> x = y)
        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`;;

let IMAGE_DIFF_INJ_ALT = `!f:A->B s t.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\ t SUBSET s
        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`;;

let IMAGE_DELETE_INJ = `!f:A->B s a.
        (!x. x IN s /\ f x = f a ==> x = a)
        ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a`;;

let IMAGE_DELETE_INJ_ALT = `!f:A->B s a.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\ a IN s
        ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a`;;

let IMAGE_EQ_EMPTY = `!(f:A->B) s. (IMAGE f s = {}) <=> (s = {})`;;

let FORALL_IN_IMAGE_2 = `!(f:A->B) P s. (!x y. x IN IMAGE f s /\ y IN IMAGE f s ==> P x y) <=>
                 (!x y. x IN s /\ y IN s ==> P (f x) (f y))`;;

let IMAGE_CONST = `!(s:A->bool) (c:B). IMAGE (\x. c) s = if s = {} then {} else {c}`;;

let SIMPLE_IMAGE = `!(f:A->B) s. {f x | x IN s} = IMAGE f s`;;

let SIMPLE_IMAGE_GEN = `!(f:A->B) P. {f x | P x} = IMAGE f {x | P x}`;;

let IMAGE_UNIONS = `!(f:A->B) s. IMAGE f (UNIONS s) = UNIONS (IMAGE (IMAGE f) s)`;;

let FUN_IN_IMAGE = `!(f:A->B) s x. x IN s ==> f(x) IN IMAGE f s`;;

let SURJECTIVE_IMAGE_EQ = `!(f:A->B) s t.
        (!y. y IN t ==> ?x. f x = y) /\ (!x. (f x) IN t <=> x IN s)
        ==> IMAGE f s = t`;;

let IMAGE_EQ = `!(f:A->B) g s. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`;;

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let EMPTY_GSPEC = `{x:A | F} = {}`;;

let UNIV_GSPEC = `{x | T} = (:A)`;;

let SING_GSPEC = `(!a:A. {x | x = a} = {a}) /\
   (!a:A. {x | a = x} = {a})`;;

let SING_ALT = `!s:A->bool. (?x. s = {x}) <=> ?!x. x IN s`;;

let IN_GSPEC = `!s:A->bool. {x | x IN s} = s`;;

let IN_ELIM_PAIR_THM = `!(P:A->B->bool) a b. (a,b) IN {(x,y) | P x y} <=> P a b`;;

let IN_ELIM_TRIPLE_THM = `(!(P:A->B->C->bool) a b c. (a,b,c) IN {(x,y,z) | P x y z} <=> P a b c) /\
   (!(P:A->B->C->bool) a b c. ((a,b),c) IN {((x,y),z) | P x y z} <=> P a b c)`;;

let IN_ELIM_QUAD_THM = `(!(P:A->B->C->D->bool) a b c d.
        (a,b,c,d) IN {w,x,y,z | P w x y z} <=> P a b c d) /\
   (!(P:A->B->C->D->bool) a b c d.
        ((a,b),(c,d)) IN {(w,x),(y,z) | P w x y z} <=> P a b c d) /\
   (!(P:A->B->C->D->bool) a b c d.
        (((a,b),c),d) IN {(((w,x),y),z) | P w x y z} <=> P a b c d)`;;

let SET_PAIR_THM = `!(P:A#B->bool). {p | P p} = {(a,b) | P(a,b)}`;;

let SET_PROVE_CASES = `!P:(A->bool)->bool.
       P {} /\ (!a s. ~(a IN s) ==> P(a INSERT s))
       ==> !s. P s`;;

let UNIONS_SINGS_GEN = `!P:A->bool. UNIONS {{x} | P x} = {x | P x}`;;

let UNIONS_SINGS = `!s:A->bool. UNIONS {{x} | x IN s} = s`;;

let IMAGE_INTERS = `!(f:A->B) s.
        ~(s = {}) /\
        (!x y. x IN UNIONS s /\ y IN UNIONS s /\ f x = f y ==> x = y)
        ==> IMAGE f (INTERS s) = INTERS(IMAGE (IMAGE f) s)`;;

let DIFF_INTERS = `!(u:A->bool) s. u DIFF INTERS s = UNIONS {u DIFF t | t IN s}`;;

let INTERS_UNIONS = `!s. INTERS s = UNIV DIFF (UNIONS {(:A) DIFF t | t IN s})`;;

let UNIONS_INTERS = `!s. UNIONS s = UNIV DIFF (INTERS {(:A) DIFF t | t IN s})`;;

let UNIONS_DIFF = `!s t:A->bool. UNIONS s DIFF t = UNIONS {x DIFF t | x IN s}`;;

let DIFF_UNIONS = `!(u:A->bool) s. u DIFF UNIONS s = u INTER INTERS {u DIFF t | t IN s}`;;

let DIFF_UNIONS_NONEMPTY = `!(u:A->bool) s. ~(s = {}) ==> u DIFF UNIONS s = INTERS {u DIFF t | t IN s}`;;

let INTERS_OVER_UNIONS = `!f:A->(B->bool)->bool s.
        INTERS { UNIONS(f x) | x IN s} =
        UNIONS { INTERS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}`;;

let INTER_INTERS = `(!f s:A->bool.
        s INTER INTERS f =
        if f = {} then s else INTERS {s INTER t | t IN f}) /\
   (!f s:A->bool.
        INTERS f INTER s =
        if f = {} then s else INTERS {t INTER s | t IN f})`;;

let UNIONS_OVER_INTERS = `!f:A->(B->bool)->bool s.
        UNIONS { INTERS(f x) | x IN s} =
        INTERS { UNIONS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}`;;

let UNIONS_EQ_INTERS = `!f:(A->bool)->bool. UNIONS f = INTERS f <=> ?s. f = {s}`;;

let EXISTS_UNIQUE_UNIONS_INTERS = `!P. (?!s:A->bool. P s) <=> UNIONS {s | P s} = INTERS {s | P s}`;;

let IMAGE_INTERS_SUBSET = `!(f:A->B) g. IMAGE f (INTERS g) SUBSET INTERS (IMAGE (IMAGE f) g)`;;

let IMAGE_INTER_SUBSET = `!(f:A->B) s t. IMAGE f (s INTER t) SUBSET IMAGE f s INTER IMAGE f t`;;

let IMAGE_INTER_SATURATED_GEN = `!f:A->B s t u.
        {x | x IN u /\ f(x) IN IMAGE f s} SUBSET s /\ t SUBSET u \/
        {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t /\ s SUBSET u
        ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t`;;

let IMAGE_INTERS_SATURATED_GEN = `!f:A->B g s u.
        ~(g = {}) /\
        (!t. t IN g ==> t SUBSET u) /\
        (!t. t IN g DELETE s ==> {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t)
        ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)`;;

let IMAGE_INTER_SATURATED = `!f:A->B s t.
        {x | f(x) IN IMAGE f s} SUBSET s \/ {x | f(x) IN IMAGE f t} SUBSET t
         ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t`;;

let IMAGE_INTERS_SATURATED = `!f:A->B g s.
        ~(g = {}) /\ (!t. t IN g DELETE s ==> {x | f(x) IN IMAGE f t} SUBSET t)
        ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)`;;

(* ------------------------------------------------------------------------- *)
(* Stronger form of induction is sometimes handy.                            *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_STRONG = `!P:(A->bool)->bool.
        P {} /\ (!x s. P s /\ ~(x IN s) /\ FINITE s ==> P(x INSERT s))
        ==> !s. FINITE s ==> P s`;;

(* ------------------------------------------------------------------------- *)
(* Useful general properties of functions.                                   *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_ON_ALT = `!P f:A->B.
        (!x y. P x /\ P y /\ f x = f y ==> x = y) <=>
        (!x y. P x /\ P y ==> (f x = f y <=> x = y))`;;

let INJECTIVE_ALT = `!f:A->B. (!x y. f x = f y ==> x = y) <=> (!x y. f x = f y <=> x = y)`;;

let SURJECTIVE_ON_RIGHT_INVERSE = `!(f:A->B) t.
        (!y. y IN t ==> ?x. x IN s /\ (f(x) = y)) <=>
        (?g. !y. y IN t ==> g(y) IN s /\ (f(g(y)) = y))`;;

let INJECTIVE_ON_LEFT_INVERSE = `!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) <=>
         (?g. !x. x IN s ==> (g(f(x)) = x))`;;

let BIJECTIVE_ON_LEFT_RIGHT_INVERSE = `!(f:A->B) s t.
        (!x. x IN s ==> f(x) IN t)
        ==> ((!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
             (!y. y IN t ==> ?x. x IN s /\ f x = y) <=>
            ?g. (!y. y IN t ==> g(y) IN s) /\
                (!y. y IN t ==> (f(g(y)) = y)) /\
                (!x. x IN s ==> (g(f(x)) = x)))`;;

let SURJECTIVE_RIGHT_INVERSE = `!f:A->B. (!y. ?x. f(x) = y) <=> (?g. !y. f(g(y)) = y)`;;

let INJECTIVE_LEFT_INVERSE = `!f:A->B. (!x y. f x = f y ==> x = y) <=> (?g. !x. g(f(x)) = x)`;;

let BIJECTIVE_LEFT_RIGHT_INVERSE = `!f:A->B.
       (!x y. f(x) = f(y) ==> x = y) /\ (!y. ?x. f x = y) <=>
       ?g. (!y. f(g(y)) = y) /\ (!x. g(f(x)) = x)`;;

let FUNCTION_FACTORS_LEFT_GEN = `!P (f:A->B) (g:A->C).
        (!x y. P x /\ P y /\ g x = g y ==> f x = f y) <=>
        (?h. !x. P x ==> f(x) = h(g x))`;;

let FUNCTION_FACTORS_LEFT = `!(f:A->B) (g:A->C). (!x y. g x = g y ==> f x = f y) <=> ?h. f = h o g`;;

let FUNCTION_FACTORS_RIGHT_GEN = `!P (f:A->C) (g:B->C).
        (!x. P x ==> ?y. g(y) = f(x)) <=>
        (?h. !x. P x ==> f(x) = g(h x))`;;

let FUNCTION_FACTORS_RIGHT = `!(f:A->C) (g:B->C). (!x. ?y. g(y) = f(x)) <=> ?h. f = g o h`;;

let SURJECTIVE_FORALL_THM = `!f:A->B. (!y. ?x. f x = y) <=> (!P. (!x. P(f x)) <=> (!y. P y))`;;

let SURJECTIVE_EXISTS_THM = `!f:A->B. (!y. ?x. f x = y) <=> (!P. (?x. P(f x)) <=> (?y. P y))`;;

let SURJECTIVE_IMAGE_THM = `!f:A->B. (!y. ?x. f x = y) <=> (!P. IMAGE f {x | P(f x)} = {x | P x})`;;

let IMAGE_INJECTIVE_IMAGE_OF_SUBSET = `!f:A->B s.
     ?t. t SUBSET s /\
         IMAGE f s = IMAGE f t /\
         (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y)`;;

(* ------------------------------------------------------------------------- *)
(* Basic combining theorems for finite sets.                                 *)
(* ------------------------------------------------------------------------- *)

let FINITE_EMPTY = `FINITE ({}:A->bool)`;;

let FINITE_SUBSET = `!(s:A->bool) t. FINITE t /\ s SUBSET t ==> FINITE s`;;

let FINITE_RESTRICT = `!s:A->bool P. FINITE s ==> FINITE {x | x IN s /\ P x}`;;

let FINITE_UNION_IMP = `!(s:A->bool) t. FINITE s /\ FINITE t ==> FINITE (s UNION t)`;;

let FINITE_UNION = `!(s:A->bool) t. FINITE(s UNION t) <=> FINITE(s) /\ FINITE(t)`;;

let FINITE_INTER = `!(s:A->bool) t. FINITE s \/ FINITE t ==> FINITE (s INTER t)`;;

let FINITE_INSERT = `!(s:A->bool) x. FINITE (x INSERT s) <=> FINITE s`;;

let FINITE_SING = `!a:A. FINITE {a}`;;

let FINITE_DELETE_IMP = `!(s:A->bool) x. FINITE s ==> FINITE (s DELETE x)`;;

let FINITE_DELETE = `!(s:A->bool) x. FINITE (s DELETE x) <=> FINITE s`;;

let FINITE_FINITE_UNIONS = `!s:(A->bool)->bool.
        FINITE(s) ==> (FINITE(UNIONS s) <=> (!t. t IN s ==> FINITE(t)))`;;

let FINITE_IMAGE_EXPAND = `!(f:A->B) s. FINITE s ==> FINITE {y | ?x. x IN s /\ (y = f x)}`;;

let FINITE_IMAGE = `!(f:A->B) s. FINITE s ==> FINITE (IMAGE f s)`;;

let FINITE_IMAGE_INJ_GENERAL = `!(f:A->B) A s.
        (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
        FINITE A
        ==> FINITE {x | x IN s /\ f(x) IN A}`;;

let FINITE_FINITE_PREIMAGE_GENERAL = `!f:A->B s t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | x IN s /\ f(x) = y})
        ==> FINITE {x | x IN s /\ f(x) IN t}`;;

let FINITE_FINITE_PREIMAGE = `!f:A->B t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | f(x) = y})
        ==> FINITE {x | f(x) IN t}`;;

let FINITE_IMAGE_INJ_EQ = `!(f:A->B) s.
        (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y)
        ==> (FINITE(IMAGE f s) <=> FINITE s)`;;

let FINITE_IMAGE_INJ = `!(f:A->B) A.
        (!x y. f(x) = f(y) ==> x = y) /\ FINITE A
        ==> FINITE {x | f(x) IN A}`;;

let FINITE_IMAGE_GEN = `!(f:A->B) (g:A->C) s t.
        IMAGE f s SUBSET t /\ FINITE t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> g x = g y)
        ==> FINITE(IMAGE g s)`;;

let INFINITE_IMAGE = `!f:A->B s.
        INFINITE s /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> INFINITE (IMAGE f s)`;;

let INFINITE_IMAGE_INJ = `!f:A->B. (!x y. (f x = f y) ==> (x = y))
            ==> !s. INFINITE s ==> INFINITE(IMAGE f s)`;;

let INFINITE_NONEMPTY = `!s:A->bool. INFINITE(s) ==> ~(s = EMPTY)`;;

let INFINITE_DIFF_FINITE = `!s:A->bool t. INFINITE(s) /\ FINITE(t) ==> INFINITE(s DIFF t)`;;

let SUBSET_IMAGE_INJ = `!f:A->B s t.
        s SUBSET (IMAGE f t) <=>
        ?u. u SUBSET t /\
            (!x y. x IN u /\ y IN u ==> (f x = f y <=> x = y)) /\
            s = IMAGE f u`;;

let SUBSET_IMAGE = `!f:A->B s t. s SUBSET (IMAGE f t) <=> ?u. u SUBSET t /\ (s = IMAGE f u)`;;

let EXISTS_SUBSET_IMAGE = `!P (f:A->B) s.
    (?t. t SUBSET IMAGE f s /\ P t) <=> (?t. t SUBSET s /\ P (IMAGE f t))`;;

let FORALL_SUBSET_IMAGE = `!P (f:A->B) s.
        (!t. t SUBSET IMAGE f s ==> P t) <=>
        (!t. t SUBSET s ==> P(IMAGE f t))`;;

let EXISTS_SUBSET_IMAGE_INJ = `!P (f:A->B) s.
    (?t. t SUBSET IMAGE f s /\ P t) <=>
    (?t. t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))`;;

let FORALL_SUBSET_IMAGE_INJ = `!P (f:A->B) s.
        (!t. t SUBSET IMAGE f s ==> P t) <=>
        (!t. t SUBSET s /\
             (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
             ==> P(IMAGE f t))`;;

let EXISTS_FINITE_SUBSET_IMAGE_INJ = `!P (f:A->B) s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))`;;

let FORALL_FINITE_SUBSET_IMAGE_INJ = `!P (f:A->B) s.
        (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
        (!t. FINITE t /\ t SUBSET s /\
             (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
             ==> P(IMAGE f t))`;;

let EXISTS_FINITE_SUBSET_IMAGE = `!P (f:A->B) s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\ P (IMAGE f t))`;;

let FORALL_FINITE_SUBSET_IMAGE = `!P (f:A->B) s.
        (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
        (!t. FINITE t /\ t SUBSET s ==> P(IMAGE f t))`;;

let FINITE_SUBSET_IMAGE = `!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s) <=>
        ?s'. FINITE s' /\ s' SUBSET s /\ (t = IMAGE f s')`;;

let FINITE_SUBSET_IMAGE_IMP = `!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s)
        ==> ?s'. FINITE s' /\ s' SUBSET s /\ t SUBSET (IMAGE f s')`;;

let FINITE_IMAGE_EQ = `!(f:A->B) s. FINITE(IMAGE f s) <=>
                ?t. FINITE t /\ t SUBSET s /\ IMAGE f s = IMAGE f t`;;

let FINITE_IMAGE_EQ_INJ = `!(f:A->B) s. FINITE(IMAGE f s) <=>
                ?t. FINITE t /\ t SUBSET s /\ IMAGE f s = IMAGE f t /\
                    (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))`;;

let FINITE_DIFF = `!s t:A->bool. FINITE s ==> FINITE(s DIFF t)`;;

let INFINITE_SUPERSET = `!s t:A->bool. INFINITE s /\ s SUBSET t ==> INFINITE t`;;

let FINITE_TRANSITIVITY_CHAIN = `!R s:A->bool.
        FINITE s /\
        (!x. ~(R x x)) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!x. x IN s ==> ?y. y IN s /\ R x y)
        ==> s = {}`;;

let UNIONS_MAXIMAL_SETS = `!f. FINITE f
       ==> UNIONS {t:A->bool | t IN f /\ !u. u IN f ==> ~(t PSUBSET u)} =
           UNIONS f`;;

let FINITE_SUBSET_UNIONS = `!f s:A->bool.
        FINITE s /\ s SUBSET UNIONS f
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ s SUBSET UNIONS f'`;;

let UNIONS_IN_CHAIN = `!f:(A->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> UNIONS f IN f`;;

let INTERS_IN_CHAIN = `!f:(A->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> INTERS f IN f`;;

let FINITE_SUBSET_UNIONS_DIRECTED_EQ = `!f s:A->bool.
        ~(f = {}) /\
        (!t u. t IN f /\ u IN f
               ==> ?v. v IN f /\ t SUBSET v /\ u SUBSET v) /\
        FINITE s
        ==> (s SUBSET UNIONS f <=> ?t. t IN f /\ s SUBSET t)`;;

let FINITE_SUBSET_UNIONS_CHAIN_EQ = time prove
 (`!f s:A->bool.
        ~(f = {}) /\
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t) /\
        FINITE s
        ==> (s SUBSET UNIONS f <=> ?t. t IN f /\ s SUBSET t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET_UNIONS_DIRECTED_EQ THEN
  ASM_MESON_TAC[SUBSET_REFL]);;

let FINITE_SUBSET_UNIONS_CHAIN = `!f s:A->bool.
        FINITE s /\ s SUBSET UNIONS f /\ ~(f = {}) /\
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t)
        ==> ?t. t IN f /\ s SUBSET t`;;

(* ------------------------------------------------------------------------- *)
(* Recursion over finite sets; based on Ching-Tsun's code (archive 713).     *)
(* ------------------------------------------------------------------------- *)

let FINREC = new_recursive_definition num_RECURSION
  `(FINREC (f:A->B->B) b s a 0 <=> (s = {}) /\ (a = b)) /\
   (FINREC (f:A->B->B) b s a (SUC n) <=>
                ?x c. x IN s /\
                      FINREC f b (s DELETE x) c n  /\
                      (a = f x c))`;;

let FINREC_1_LEMMA = `!(f:A->B->B) b s a. FINREC f b s a (SUC 0) <=> ?x. s = {x} /\ a = f x b`;;

let FINREC_SUC_LEMMA = `!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n s z.
                FINREC f b s z (SUC n)
                ==> !x. x IN s ==> ?w. FINREC f b (s DELETE x) w n /\
                                       (z = f x w)`;;

let FINREC_UNIQUE_LEMMA = `!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n1 n2 s a1 a2.
                FINREC f b s a1 n1 /\ FINREC f b s a2 n2
                ==> (a1 = a2) /\ (n1 = n2)`;;

let FINREC_EXISTS_LEMMA = `!(f:A->B->B) b s. FINITE s ==> ?a n. FINREC f b s a n`;;

let FINREC_FUN_LEMMA = `!P (R:A->B->C->bool).
       (!s. P s ==> ?a n. R s a n) /\
       (!n1 n2 s a1 a2. R s a1 n1 /\ R s a2 n2 ==> (a1 = a2) /\ (n1 = n2))
       ==> ?f. !s a. P s ==> ((?n. R s a n) <=> (f s = a))`;;

let FINREC_FUN = `!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !s x. FINITE s /\ x IN s
                      ==> (g s = f x (g (s DELETE x)))`;;

let SET_RECURSION_LEMMA = `!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !x s. FINITE s
                      ==> (g (x INSERT s) =
                                if x IN s then g s else f x (g s))`;;

let ITSET = new_definition
  `ITSET (f:A->B->B) s b =
        (@g. (g {} = b) /\
             !x s. FINITE s
                   ==> (g (x INSERT s) = if x IN s then g s else f x (g s)))
        s`;;

let FINITE_RECURSION = `!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f (x INSERT s) b =
                       if x IN s then ITSET f s b
                                 else f x (ITSET f s b))`;;

let FINITE_RECURSION_DELETE = `!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f s b =
                       if x IN s then f x (ITSET f (s DELETE x) b)
                                 else ITSET f (s DELETE x) b)`;;

let ITSET_EQ = `!s (f:A->B->B) g b.
        FINITE(s) /\ (!x. x IN s ==> (f x = g x)) /\
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s))) /\
        (!x y s. ~(x = y) ==> (g x (g y s) = g y (g x s)))
        ==> (ITSET f s b = ITSET g s b)`;;

(* ------------------------------------------------------------------------- *)
(* Cardinality.                                                              *)
(* ------------------------------------------------------------------------- *)

let CARD = new_definition
 `CARD (s:A->bool) = ITSET (\x n. SUC n) s 0`;;

let CARD_CLAUSES = `(CARD ({}:A->bool) = 0) /\
   (!(x:A) s. FINITE s ==>
                 (CARD (x INSERT s) =
                      if x IN s then CARD s else SUC(CARD s)))`;;

let CARD_UNION = `!(s:A->bool) t. FINITE(s) /\ FINITE(t) /\ (s INTER t = EMPTY)
         ==> (CARD (s UNION t) = CARD s + CARD t)`;;

let CARD_DELETE = `!x:A s. FINITE(s)
           ==> (CARD(s DELETE x) = if x IN s then CARD(s) - 1 else CARD(s))`;;

let CARD_UNION_EQ = `!s t u:A->bool.
        FINITE u /\ s INTER t = {} /\ s UNION t = u
        ==> (CARD s + CARD t = CARD u)`;;

let CARD_DIFF = `!s t:A->bool. FINITE s /\ t SUBSET s ==> CARD(s DIFF t) = CARD s - CARD t`;;

let CARD_EQ_0 = `!s:A->bool. FINITE s ==> ((CARD s = 0) <=> (s = {}))`;;

let CARD_SING = `!a:A. CARD {a} = 1`;;

(* ------------------------------------------------------------------------- *)
(* A stronger still form of induction where we get to choose the element.    *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_DELETE = `!P. P {} /\
       (!s. FINITE s /\ ~(s = {}) ==> ?x. x IN s /\ (P(s DELETE x) ==> P s))
       ==> !s:A->bool. FINITE s ==> P s`;;

(* ------------------------------------------------------------------------- *)
(* Relational form is often more useful.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE = new_definition
  `(s:A->bool) HAS_SIZE n <=> FINITE s /\ CARD s = n`;;

let HAS_SIZE_CARD = `!(s:A->bool) n. s HAS_SIZE n ==> CARD s = n`;;

let HAS_SIZE_0 = `!(s:A->bool). s HAS_SIZE 0 <=> (s = {})`;;

let HAS_SIZE_SUC = `!(s:A->bool) n. s HAS_SIZE (SUC n) <=>
                   ~(s = {}) /\ !a. a IN s ==> (s DELETE a) HAS_SIZE n`;;

let HAS_SIZE_UNION = `!(s:A->bool) t m n.
        s HAS_SIZE m /\ t HAS_SIZE n /\ DISJOINT s t
        ==> (s UNION t) HAS_SIZE (m + n)`;;

let HAS_SIZE_DIFF = `!(s:A->bool) t m n.
        s HAS_SIZE m /\ t HAS_SIZE n /\ t SUBSET s
        ==> (s DIFF t) HAS_SIZE (m - n)`;;

let HAS_SIZE_UNIONS = `!s t:A->B->bool m n.
        s HAS_SIZE m /\
        (!x. x IN s ==> t(x) HAS_SIZE n) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (t x) (t y))
        ==> UNIONS {t(x) | x IN s} HAS_SIZE (m * n)`;;

let FINITE_HAS_SIZE = `!s:A->bool. FINITE s <=> s HAS_SIZE CARD s`;;

(* ------------------------------------------------------------------------- *)
(* This is often more useful as a rewrite.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CLAUSES = `(s HAS_SIZE 0 <=> s = {}) /\
   (s HAS_SIZE (SUC n) <=>
        ?(a:A) t. t HAS_SIZE n /\ ~(a IN t) /\ (s = a INSERT t))`;;

(* ------------------------------------------------------------------------- *)
(* Produce an explicit expansion for "s HAS_SIZE n" for numeral n.           *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CONV =
  let pth = `(~((a:A) IN {}) /\ P <=> P) /\
     (~(a IN {b}) /\ P <=> ~(a = b) /\ P) /\
     (~(a IN (b INSERT cs)) /\ P <=> ~(a = b) /\ ~(a IN cs) /\ P)`;;

let CARD_SUBSET = `!(a:A->bool) b. a SUBSET b /\ FINITE(b) ==> CARD(a) <= CARD(b)`;;

let CARD_SUBSET_LE = `!(a:A->bool) b. FINITE b /\ a SUBSET b /\ CARD b <= CARD a ==> a = b`;;

let SUBSET_CARD_EQ = `!s t:A->bool. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)`;;

let FINITE_CARD_LE_SUBSET = `!s (t:A->bool) n.
        s SUBSET t /\ FINITE t /\ CARD t <= n
        ==> FINITE s /\ CARD s <= n`;;

let CARD_PSUBSET = `!(a:A->bool) b. a PSUBSET b /\ FINITE(b) ==> CARD(a) < CARD(b)`;;

let CARD_PSUBSET_IMP = `!a b:A->bool. a SUBSET b /\ ~(CARD a = CARD b) ==> a PSUBSET b`;;

let CARD_PSUBSET_EQ = `!a b:A->bool. FINITE b /\ a SUBSET b ==> (a PSUBSET b <=> CARD a < CARD b)`;;

let CARD_UNION_LE = `!s t:A->bool.
        FINITE s /\ FINITE t ==> CARD(s UNION t) <= CARD(s) + CARD(t)`;;

let FINITE_CARD_LE_UNION = `!s (t:A->bool) m n.
        (FINITE s /\ CARD s <= m) /\
        (FINITE t /\ CARD t <= n)
        ==> FINITE(s UNION t) /\ CARD(s UNION t) <= m + n`;;

let CARD_UNIONS_LE = `!s t:A->B->bool m n.
        s HAS_SIZE m /\ (!x. x IN s ==> FINITE(t x) /\ CARD(t x) <= n)
        ==> CARD(UNIONS {t(x) | x IN s}) <= m * n`;;

let CARD_UNION_GEN = `!s t:A->bool.
        FINITE s /\ FINITE t
        ==> CARD(s UNION t) = (CARD(s) + CARD(t)) - CARD(s INTER t)`;;

let CARD_UNION_OVERLAP_EQ = `!s t:A->bool.
        FINITE s /\ FINITE t
        ==> (CARD(s UNION t) = CARD s + CARD t <=> s INTER t = {})`;;

let CARD_UNION_OVERLAP = `!s t:A->bool.
        FINITE s /\ FINITE t /\ CARD(s UNION t) < CARD(s) + CARD(t)
        ==> ~(s INTER t = {})`;;

(* ------------------------------------------------------------------------- *)
(* Cardinality of image under maps, injective or general.                    *)
(* ------------------------------------------------------------------------- *)

let CARD_IMAGE_INJ = `!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                FINITE s ==> (CARD (IMAGE f s) = CARD s)`;;

let HAS_SIZE_IMAGE_INJ = `!(f:A->B) s n.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\ s HAS_SIZE n
        ==> (IMAGE f s) HAS_SIZE n`;;

let CARD_IMAGE_LE = `!(f:A->B) s. FINITE s ==> CARD(IMAGE f s) <= CARD s`;;

let FINITE_CARD_LE_IMAGE = `!(f:A->B) s n.
        FINITE s /\ CARD s <= n ==> FINITE(IMAGE f s) /\ CARD(IMAGE f s) <= n`;;

let CARD_IMAGE_INJ_EQ = `!f:A->B s t.
        FINITE s /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> ?!x. x IN s /\ f(x) = y)
        ==> CARD t = CARD s`;;

let CARD_SUBSET_IMAGE = `!(f:A->B) s t. FINITE t /\ s SUBSET IMAGE f t ==> CARD s <= CARD t`;;

let HAS_SIZE_IMAGE_INJ_EQ = `!(f:A->B) s n.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n)`;;

let CARD_IMAGE_EQ_INJ = `!f:A->B s.
        FINITE s
        ==> (CARD(IMAGE f s) = CARD s <=>
             !x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`;;

let EXISTS_SMALL_SUBSET_IMAGE_INJ = `!P (f:A->B) s n.
    (?t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ CARD t < n /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))`;;

let FORALL_SMALL_SUBSET_IMAGE_INJ = `!P (f:A->B) s n.
    (!t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s ==> P t) <=>
    (!t. FINITE t /\ CARD t < n /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
         ==> P (IMAGE f t))`;;

let EXISTS_SMALL_SUBSET_IMAGE = `!P (f:A->B) s n.
    (?t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ CARD t < n /\ t SUBSET s /\
         P (IMAGE f t))`;;

let FORALL_SMALL_SUBSET_IMAGE = `!P (f:A->B) s n.
    (!t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s ==> P t) <=>
    (!t. FINITE t /\ CARD t < n /\ t SUBSET s ==> P (IMAGE f t))`;;

let CARD_IMAGE_LE2 = `!(f:A->B) (g:A->C) s.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ g x = g y ==> f x = f y)
        ==> CARD(IMAGE f s) <= CARD(IMAGE g s)`;;

let CARD_IMAGE_LT2 = `!(f:A->B) (g:A->C) s.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ g x = g y ==> f x = f y) /\
        ~(!x y. x IN s /\ y IN s /\ f x = f y ==> g x = g y)
        ==> CARD(IMAGE f s) < CARD(IMAGE g s)`;;

(* ------------------------------------------------------------------------- *)
(* Choosing a smaller subset of a given size.                                *)
(* ------------------------------------------------------------------------- *)

let CHOOSE_SUBSET_STRONG = `!n s:A->bool.
        (FINITE s ==> n <= CARD s) ==> ?t. t SUBSET s /\ t HAS_SIZE n`;;

let CHOOSE_SUBSET_EQ = `!n s:A->bool.
     (FINITE s ==> n <= CARD s) <=> (?t. t SUBSET s /\ t HAS_SIZE n)`;;

let CHOOSE_SUBSET = `!s:A->bool. FINITE s ==> !n. n <= CARD s ==> ?t. t SUBSET s /\ t HAS_SIZE n`;;

let CHOOSE_SUBSET_BETWEEN = `!n s u:A->bool.
        s SUBSET u /\ FINITE s /\ CARD s <= n /\ (FINITE u ==> n <= CARD u)
        ==> ?t. s SUBSET t /\ t SUBSET u /\ t HAS_SIZE n`;;

let CARD_LE_UNIONS_CHAIN = `!(f:(A->bool)->bool) n.
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t) /\
        (!t. t IN f ==> FINITE t /\ CARD t <= n)
        ==> FINITE(UNIONS f) /\ CARD(UNIONS f) <= n`;;

let CARD_LE_1 = `!s:A->bool. FINITE s /\ CARD s <= 1 <=> ?a. s SUBSET {a}`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the parity of the set of fixed points of an involution.      *)
(* ------------------------------------------------------------------------- *)

let INVOLUTION_EVEN_NOFIXPOINTS = `!f (s:A->bool).
        FINITE s /\ (!x. x IN s ==> f x IN s /\ ~(f x = x) /\ f(f x) = x)
        ==> EVEN(CARD s)`;;

let INVOLUTION_EVEN_FIXPOINTS = `!f (s:A->bool).
        FINITE s /\ (!x. x IN s ==> f x IN s /\ f(f x) = x)
        ==> (EVEN(CARD {x | x IN s /\ f x = x}) <=> EVEN(CARD s))`;;

(* ------------------------------------------------------------------------- *)
(* Cardinality of product.                                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_PRODUCT_DEPENDENT = `!s m t n.
         s HAS_SIZE m /\ (!x. x IN s ==> t(x) HAS_SIZE n)
         ==> {(x:A,y:B) | x IN s /\ y IN t(x)} HAS_SIZE (m * n)`;;

let FINITE_PRODUCT_DEPENDENT = `!f:A->B->C s t.
        FINITE s /\ (!x. x IN s ==> FINITE(t x))
        ==> FINITE {f x y | x IN s /\ y IN (t x)}`;;

let FINITE_PRODUCT = `!s t. FINITE s /\ FINITE t ==> FINITE {(x:A,y:B) | x IN s /\ y IN t}`;;

let CARD_PRODUCT = `!s t. FINITE s /\ FINITE t
         ==> (CARD {(x:A,y:B) | x IN s /\ y IN t} = CARD s * CARD t)`;;

let HAS_SIZE_PRODUCT = `!s m t n. s HAS_SIZE m /\ t HAS_SIZE n
             ==> {(x:A,y:B) | x IN s /\ y IN t} HAS_SIZE (m * n)`;;

(* ------------------------------------------------------------------------- *)
(* Actually introduce a Cartesian product operation.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("CROSS",(22,"right"));;

let CROSS = new_definition
 `(s:A->bool) CROSS (t:B->bool) = {x,y | x IN s /\ y IN t}`;;

let IN_CROSS = `!(x:A) (y:B) s t. (x,y) IN (s CROSS t) <=> x IN s /\ y IN t`;;

let HAS_SIZE_CROSS = `!(s:A->bool) (t:B->bool) m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s CROSS t) HAS_SIZE (m * n)`;;

let FINITE_CROSS = `!(s:A->bool) (t:B->bool). FINITE s /\ FINITE t ==> FINITE(s CROSS t)`;;

let CARD_CROSS = `!(s:A->bool) (t:B->bool). FINITE s /\ FINITE t ==> CARD(s CROSS t) = CARD s * CARD t`;;

let CROSS_EQ_EMPTY = `!(s:A->bool) (t:B->bool). s CROSS t = {} <=> s = {} \/ t = {}`;;

let CROSS_EMPTY = `(!s:A->bool. s CROSS {} = {}) /\ (!t:B->bool. {} CROSS t = {})`;;

let CROSS_SING = `!x:A y:B. {x} CROSS {y} = {(x,y)}`;;

let CROSS_UNIV = `(:A) CROSS (:B) = (:A#B)`;;

let FINITE_CROSS_EQ = `!s:A->bool t:B->bool.
        FINITE(s CROSS t) <=> s = {} \/ t = {} \/ FINITE s /\ FINITE t`;;

let INFINITE_CROSS_EQ = `!(s:A->bool) (t:B->bool).
        INFINITE(s CROSS t) <=>
        ~(s = {}) /\ INFINITE t \/ INFINITE s /\ ~(t = {})`;;

let FINITE_CROSS_UNIV = `FINITE(:A#B) <=> FINITE(:A) /\ FINITE(:B)`;;

let INFINITE_CROSS_UNIV = `INFINITE(:A#B) <=> INFINITE(:A) \/ INFINITE(:B)`;;

let FINITE_UNIV_PAIR = `FINITE(:A#A) <=> FINITE(:A)`;;

let INFINITE_UNIV_PAIR = `INFINITE(:A#A) <=> INFINITE(:A)`;;

let FORALL_IN_CROSS = `!P s t. (!z:A#B. z IN s CROSS t ==> P z) <=>
           (!x y. x IN s /\ y IN t ==> P(x,y))`;;

let EXISTS_IN_CROSS = `!P s t. (?z:A#B. z IN s CROSS t /\ P z) <=>
           (?x y. x IN s /\ y IN t /\ P(x,y))`;;

let SUBSET_CROSS = `!(s:A->bool) (t:B->bool) s' t'.
        s CROSS t SUBSET s' CROSS t' <=>
        s = {} \/ t = {} \/ s SUBSET s' /\ t SUBSET t'`;;

let CROSS_MONO = `!(s:A->bool) (t:B->bool) s' t'. s SUBSET s' /\ t SUBSET t' ==> s CROSS t SUBSET s' CROSS t'`;;

let CROSS_EQ = `!s s':A->bool t t':B->bool.
        s CROSS t = s' CROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/ s = s' /\ t = t'`;;

let IMAGE_FST_CROSS = `!s:A->bool t:B->bool.
        IMAGE FST (s CROSS t) = if t = {} then {} else s`;;

let IMAGE_SND_CROSS = `!s:A->bool t:B->bool.
        IMAGE SND (s CROSS t) = if s = {} then {} else t`;;

let IMAGE_PAIRED_CROSS = `!(f:A->B) (g:C->D) s t.
         IMAGE (\(x,y). f x,g y) (s CROSS t) = (IMAGE f s) CROSS (IMAGE g t)`;;

let CROSS_INTER = `(!(s:A->bool) (t:B->bool) u.
        s CROSS (t INTER u) = (s CROSS t) INTER (s CROSS u)) /\
   (!(s:A->bool) t (u:B->bool).
        (s INTER t) CROSS u = (s CROSS u) INTER (t CROSS u))`;;

let CROSS_UNION = `(!(s:A->bool) (t:B->bool) u.
        s CROSS (t UNION u) = (s CROSS t) UNION (s CROSS u)) /\
   (!(s:A->bool) t (u:B->bool).
        (s UNION t) CROSS u = (s CROSS u) UNION (t CROSS u))`;;

let CROSS_DIFF = `(!(s:A->bool) (t:B->bool) u.
        s CROSS (t DIFF u) = (s CROSS t) DIFF (s CROSS u)) /\
   (!(s:A->bool) t (u:B->bool).
        (s DIFF t) CROSS u = (s CROSS u) DIFF (t CROSS u))`;;

let INTER_CROSS = `!(s:A->bool) s' (t:B->bool) t'.
      (s CROSS t) INTER (s' CROSS t') = (s INTER s') CROSS (t INTER t')`;;

let CROSS_UNIONS_UNIONS,CROSS_UNIONS = (CONJ_PAIR o prove)
 (`(!(f:(A->bool)->bool) (g:(B->bool)->bool).
        (UNIONS f) CROSS (UNIONS g) =
        UNIONS {s CROSS t | s IN f /\ t IN g}) /\
   (!(s:A->bool) (f:(A->bool)->bool).
        s CROSS (UNIONS f) = UNIONS {s CROSS t | t IN f}) /\
   (!(f:(A->bool)->bool) (t:B->bool).
        (UNIONS f) CROSS t = UNIONS {s CROSS t | s IN f})`,
  REWRITE_TAC[UNIONS_GSPEC; EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM;
              IN_CROSS] THEN
  SET_TAC[]);;

let CROSS_INTERS_INTERS,CROSS_INTERS = (CONJ_PAIR o prove)
 (`(!(f:(A->bool)->bool) (g:(B->bool)->bool).
        (INTERS f) CROSS (INTERS g) =
        if f = {} then INTERS {UNIV CROSS t | t IN g}
        else if g = {} then INTERS {s CROSS UNIV | s IN f}
        else INTERS {s CROSS t | s IN f /\ t IN g}) /\
   (!(s:A->bool) (f:(A->bool)->bool).
        s CROSS (INTERS f) =
        if f = {} then s CROSS UNIV else INTERS {s CROSS t | t IN f}) /\
   (!(f:(A->bool)->bool) (t:B->bool).
        (INTERS f) CROSS t =
        if f = {} then UNIV CROSS t else INTERS {s CROSS t | s IN f})`,
  REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[INTERS_GSPEC; EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM;
                  IN_CROSS; NOT_IN_EMPTY] THEN
  ASM SET_TAC[]);;

let DISJOINT_CROSS = `!s:A->bool t:B->bool s' t'.
        DISJOINT (s CROSS t) (s' CROSS t') <=>
        DISJOINT s s' \/ DISJOINT t t'`;;

(* ------------------------------------------------------------------------- *)
(* "Extensional" functions, mapping to a fixed value ARB outside the domain. *)
(* Even though these are still total, they're a conveniently better model    *)
(* of the partial function space (e.g. the space has the right cardinality). *)
(* ------------------------------------------------------------------------- *)

let ARB = new_definition
  `ARB = (@x:A. F)`;;

let EXTENSIONAL = new_definition
  `EXTENSIONAL s = {f:A->B | !x. ~(x IN s) ==> f x = ARB}`;;

let IN_EXTENSIONAL = `!s f:A->B. f IN EXTENSIONAL s <=> (!x. ~(x IN s) ==> f x = ARB)`;;

let IN_EXTENSIONAL_UNDEFINED = `!s f:A->B x. f IN EXTENSIONAL s /\ ~(x IN s) ==> f x = ARB`;;

let EXTENSIONAL_EMPTY = `EXTENSIONAL {} = {\x:A. ARB:B}`;;

let EXTENSIONAL_UNIV = `!f:A->B. EXTENSIONAL (:A) f`;;

let EXTENSIONAL_EQ = `!s f g:A->B.
     f IN EXTENSIONAL s /\ g IN EXTENSIONAL s /\ (!x. x IN s ==> f x = g x)
     ==> f = g`;;

(* ------------------------------------------------------------------------- *)
(* Restriction of a function to an EXTENSIONAL one on a subset.              *)
(* ------------------------------------------------------------------------- *)

let RESTRICTION = new_definition
  `RESTRICTION s (f:A->B) x = if x IN s then f x else ARB`;;

let RESTRICTION_THM = `!s (f:A->B). RESTRICTION s f = \x. if x IN s then f x else ARB`;;

let RESTRICTION_DEFINED = `!s f:A->B x. x IN s ==> RESTRICTION s f x = f x`;;

let RESTRICTION_UNDEFINED = `!s f:A->B x. ~(x IN s) ==> RESTRICTION s f x = ARB`;;

let RESTRICTION_EQ = `!s f:A->B x y. x IN s /\ f x = y ==> RESTRICTION s f x = y`;;

let RESTRICTION_IN_EXTENSIONAL = `!s f:A->B. RESTRICTION s f IN EXTENSIONAL s`;;

let RESTRICTION_EXTENSION = `!s f g:A->B. RESTRICTION s f = RESTRICTION s g <=>
                (!x. x IN s ==> f x = g x)`;;

let RESTRICTION_FIXPOINT = `!s f:A->B. RESTRICTION s f = f <=> f IN EXTENSIONAL s`;;

let RESTRICTION_UNIV = `!f:A->B. RESTRICTION UNIV f = f`;;

let RESTRICTION_RESTRICTION = `!s t f:A->B.
        s SUBSET t ==> RESTRICTION s (RESTRICTION t f) = RESTRICTION s f`;;

let RESTRICTION_IDEMP = `!s f:A->B. RESTRICTION s (RESTRICTION s f) = RESTRICTION s f`;;

let IMAGE_RESTRICTION = `!f:A->B s t. s SUBSET t ==> IMAGE (RESTRICTION t f) s = IMAGE f s`;;

let RESTRICTION_COMPOSE_RIGHT = `!f:A->B g:B->C s.
        RESTRICTION s (g o RESTRICTION s f) =
        RESTRICTION s (g o f)`;;

let RESTRICTION_COMPOSE_LEFT = `!f:A->B g:B->C s t.
        IMAGE f s SUBSET t
        ==> RESTRICTION s (RESTRICTION t g o f) =
            RESTRICTION s (g o f)`;;

let RESTRICTION_COMPOSE = `!f:A->B g:B->C s t.
        IMAGE f s SUBSET t
        ==> RESTRICTION s (RESTRICTION t g o RESTRICTION s f) =
            RESTRICTION s (g o f)`;;

let RESTRICTION_UNIQUE = `!s (f:A->B) g.
        RESTRICTION s f = g <=> EXTENSIONAL s g /\ !x. x IN s ==> f x = g x`;;

let RESTRICTION_UNIQUE_ALT = `!s (f:A->B) g.
        f = RESTRICTION s g <=> EXTENSIONAL s f /\ !x. x IN s ==> f x = g x`;;

(* ------------------------------------------------------------------------- *)
(* General Cartesian product / dependent function space.                     *)
(* ------------------------------------------------------------------------- *)

let cartesian_product = new_definition
 `cartesian_product k s =
        {f:K->A | EXTENSIONAL k f /\ !i. i IN k ==> f i IN s i}`;;

let IN_CARTESIAN_PRODUCT = `!k s (x:K->A).
        x IN cartesian_product k s <=>
        EXTENSIONAL k x /\ (!i. i IN k ==> x i IN s i)`;;

let CARTESIAN_PRODUCT = `!k s. cartesian_product k s =
         {f:K->A | !i. f i IN (if i IN k then s i else {ARB})}`;;

let RESTRICTION_IN_CARTESIAN_PRODUCT = `!k s (f:K->A).
        RESTRICTION k f IN cartesian_product k s <=>
        !i. i IN k ==> (f i) IN (s i)`;;

let CARTESIAN_PRODUCT_AS_RESTRICTIONS = `!k (s:K->A->bool).
      cartesian_product k s =
      {RESTRICTION k f |f| !i. i IN k ==> f i IN s i}`;;

let CARTESIAN_PRODUCT_EQ_EMPTY = `!k s:K->A->bool.
        cartesian_product k s = {} <=> ?i. i IN k /\ s i = {}`;;

let CARTESIAN_PRODUCT_EMPTY = `!(s:K->A->bool). cartesian_product {} s = {(\i. ARB)}`;;

let CARTESIAN_PRODUCT_EQ_MEMBERS = `!k s x y:K->A.
        x IN cartesian_product k s /\ y IN cartesian_product k s /\
        (!i. i IN k ==> x i = y i)
        ==> x = y`;;

let CARTESIAN_PRODUCT_EQ_MEMBERS_EQ = `!k s x y:K->A.
        x IN cartesian_product k s /\
        y IN cartesian_product k s
        ==> (x = y <=> !i. i IN k ==> x i = y i)`;;

let SUBSET_CARTESIAN_PRODUCT = `!k s t:K->A->bool.
        cartesian_product k s SUBSET cartesian_product k t <=>
        cartesian_product k s = {} \/ !i. i IN k ==> s i SUBSET t i`;;

let CARTESIAN_PRODUCT_EQ = `!k s t:K->A->bool.
        cartesian_product k s = cartesian_product k t <=>
        cartesian_product k s = {} /\ cartesian_product k t = {} \/
        !i. i IN k ==> s i = t i`;;

let INTER_CARTESIAN_PRODUCT = `!k s t:K->A->bool.
        (cartesian_product k s) INTER (cartesian_product k t) =
        cartesian_product k (\i. s i INTER t i)`;;

let CARTESIAN_PRODUCT_UNIV = `cartesian_product (:K) (\i. (:A)) = (:K->A)`;;

let CARTESIAN_PRODUCT_SINGS = `!k x:K->A. EXTENSIONAL k x ==> cartesian_product k (\i. {x i}) = {x}`;;

let CARTESIAN_PRODUCT_SINGS_GEN = `!k (x:K->A). cartesian_product k (\i. {x i}) = {RESTRICTION k x}`;;

let IMAGE_PROJECTION_CARTESIAN_PRODUCT = `!k s:K->A->bool i.
        IMAGE (\x. x i) (cartesian_product k s) =
        if cartesian_product k s = {} then {}
        else if i IN k then s i else {ARB}`;;

let FORALL_CARTESIAN_PRODUCT_ELEMENTS = `!P k s:K->A->bool.
        (!z i. z IN cartesian_product k s /\ i IN k ==> P i (z i)) <=>
        cartesian_product k s = {} \/
        (!i x. i IN k /\ x IN s i ==> P i x)`;;

let FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ = `!P k (s:K->A->bool).
        ~(cartesian_product k s = {})
        ==> ((!i x. i IN k /\ x IN s i ==> P i x) <=>
             !z i. z IN cartesian_product k s /\ i IN k ==> P i (z i))`;;

let EXISTS_CARTESIAN_PRODUCT_ELEMENT = `!P k s:K->A->bool.
        (?z. z IN cartesian_product k s /\ (!i. i IN k ==> P i (z i))) <=>
        (!i. i IN k ==> ?x. x IN (s i) /\ P i x)`;;

(* ------------------------------------------------------------------------- *)
(* Product of a family of maps.                                              *)
(* ------------------------------------------------------------------------- *)

let product_map = new_definition
 `product_map k (f:K->A->B) = \x. RESTRICTION k (\i. f i (x i))`;;

let PRODUCT_MAP_RESTRICTION = `!(f:K->A->B) k x.
        product_map k f (RESTRICTION k x) = RESTRICTION k (\i. f i (x i))`;;

let IMAGE_PRODUCT_MAP = `!(f:K->A->B) k s.
        IMAGE (product_map k f) (cartesian_product k s) =
        cartesian_product k (\i. IMAGE (f i) (s i))`;;

(* ------------------------------------------------------------------------- *)
(* Disjoint union construction for a family of sets.                         *)
(* ------------------------------------------------------------------------- *)

let disjoint_union = new_definition
 `disjoint_union (k:K->bool) (s:K->A->bool) = { (i,x) | i IN k /\ x IN s i}`;;

let SUBSET_DISJOINT_UNION = `!k (s:K->A->bool) t.
        disjoint_union k s SUBSET disjoint_union k t <=>
        !i. i IN k ==> s i SUBSET t i`;;

let DISJOINT_UNION_EQ = `!k (s:K->A->bool) t.
        disjoint_union k s = disjoint_union k t <=>
        !i. i IN k ==> s i = t i`;;

let SUBSET_DISJOINT_UNION_EXISTS = `!k (s:K->A->bool) u.
        u SUBSET disjoint_union k s <=>
        ?t. u = disjoint_union k t /\ !i. i IN k ==> t i SUBSET s i`;;

let INTER_DISJOINT_UNION = `!k s t:K->A->bool.
        (disjoint_union k s) INTER (disjoint_union k t) =
        disjoint_union k (\i. s i INTER t i)`;;

let UNION_DISJOINT_UNION = `!k s t:K->A->bool.
        (disjoint_union k s) UNION (disjoint_union k t) =
        disjoint_union k (\i. s i UNION t i)`;;

let DISJOINT_UNION_EQ_EMPTY = `!k s:K->A->bool.
        disjoint_union k s = {} <=> !i. i IN k ==> s i = {}`;;

let DISJOINT_DISJOINT_UNION = `!k s t:K->A->bool.
        DISJOINT (disjoint_union k s) (disjoint_union k t) =
        !i. i IN k ==> DISJOINT (s i) (t i)`;;

(* ------------------------------------------------------------------------- *)
(* Cardinality of functions with bounded domain (support) and range.         *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_FUNSPACE = `!d n t:B->bool m s:A->bool.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | (!x. x IN s ==> f(x) IN t) /\ (!x. ~(x IN s) ==> (f x = d))}
            HAS_SIZE (n EXP m)`;;

let CARD_FUNSPACE = `!s t. FINITE s /\ FINITE t
         ==> (CARD {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                             (!x. ~(x IN s) ==> (f x = d))} =
             (CARD t) EXP (CARD s))`;;

let FINITE_FUNSPACE = `!s t. FINITE s /\ FINITE t
         ==> FINITE {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                              (!x. ~(x IN s) ==> (f x = d))}`;;

let HAS_SIZE_FUNSPACE_UNIV = `!m n. (:A) HAS_SIZE m /\ (:B) HAS_SIZE n ==> (:A->B) HAS_SIZE (n EXP m)`;;

let CARD_FUNSPACE_UNIV = `FINITE(:A) /\ FINITE(:B) ==> CARD(:A->B) = CARD(:B) EXP CARD(:A)`;;

let FINITE_FUNSPACE_UNIV = `FINITE(:A) /\ FINITE(:B) ==> FINITE(:A->B)`;;

(* ------------------------------------------------------------------------- *)
(* Cardinality of type bool.                                                 *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_BOOL = `(:bool) HAS_SIZE 2`;;

let CARD_BOOL = `CARD(:bool) = 2`;;

let FINITE_BOOL = `FINITE(:bool)`;;

(* ------------------------------------------------------------------------- *)
(* Hence cardinality of powerset.                                            *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_POWERSET = `!(s:A->bool) n. s HAS_SIZE n ==> {t | t SUBSET s} HAS_SIZE (2 EXP n)`;;

let CARD_POWERSET = `!s:A->bool. FINITE s ==> (CARD {t | t SUBSET s} = 2 EXP (CARD s))`;;

let FINITE_POWERSET = `!s:A->bool. FINITE s ==> FINITE {t | t SUBSET s}`;;

let FINITE_POWERSET_EQ = `!s:A->bool. FINITE {t | t SUBSET s} <=> FINITE s`;;

let FINITE_RESTRICTED_SUBSETS = `!P s:A->bool. FINITE s ==> FINITE {t | t SUBSET s /\ P t}`;;

let FINITE_UNIONS = `!s:(A->bool)->bool.
        FINITE(UNIONS s) <=> FINITE s /\ (!t. t IN s ==> FINITE t)`;;

let FINITE_CARD_LE_UNIONS = `!s (t:A->B->bool) m n.
        (!x. x IN s ==> FINITE(t x) /\ CARD(t x) <= n) /\
        FINITE s /\ CARD s <= m
        ==> FINITE(UNIONS {t x | x IN s}) /\
            CARD(UNIONS {t x | x IN s}) <= m * n`;;

let POWERSET_CLAUSES = `{s:A->bool | s SUBSET {}} = {{}} /\
   (!a:A t. {s | s SUBSET (a INSERT t)} =
            {s | s SUBSET t} UNION IMAGE (\s. a INSERT s) {s | s SUBSET t})`;;

let FINITE_IMAGE_INFINITE = `!f:A->B s.
        INFINITE s /\ FINITE(IMAGE f s)
        ==> ?a. a IN s /\ INFINITE {x | x IN s /\ f x = f a}`;;

let FINITE_RESTRICTED_POWERSET = `!(s:A->bool) n.
        FINITE {t | t SUBSET s /\ t HAS_SIZE n} <=>
        FINITE s \/ n = 0`;;

let FINITE_RESTRICTED_FUNSPACE = `!s:A->bool t:B->bool k.
        FINITE s /\ FINITE t
        ==> FINITE {f | IMAGE f s SUBSET t /\ {x | ~(f x = k x)} SUBSET s}`;;

(* ------------------------------------------------------------------------- *)
(* Set of numbers is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let NUMSEG_CLAUSES_LT = `{i | i < 0} = {} /\
   (!k. {i | i < SUC k} = k INSERT {i | i < k})`;;

let HAS_SIZE_NUMSEG_LT = `!n. {m | m < n} HAS_SIZE n`;;

let CARD_NUMSEG_LT = `!n. CARD {m | m < n} = n`;;

let FINITE_NUMSEG_LT = `!n:num. FINITE {m | m < n}`;;

let NUMSEG_CLAUSES_LE = `{i | i <= 0} = {0} /\
   (!k. {i | i <= SUC k} = SUC k INSERT {i | i <= k})`;;

let HAS_SIZE_NUMSEG_LE = `!n. {m | m <= n} HAS_SIZE (n + 1)`;;

let FINITE_NUMSEG_LE = `!n. FINITE {m | m <= n}`;;

let CARD_NUMSEG_LE = `!n. CARD {m | m <= n} = n + 1`;;

let num_FINITE = `!s:num->bool. FINITE s <=> ?a. !x. x IN s ==> x <= a`;;

let num_FINITE_AVOID = `!s:num->bool. FINITE(s) ==> ?a. ~(a IN s)`;;

let num_INFINITE_EQ = `!s:num->bool. INFINITE s <=> !N. ?n. N <= n /\ n IN s`;;

let num_INFINITE = `INFINITE(:num)`;;

(* ------------------------------------------------------------------------- *)
(* Set of strings is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let string_INFINITE = `INFINITE(:string)`;;

(* ------------------------------------------------------------------------- *)
(* Non-trivial intervals of reals are infinite.                              *)
(* ------------------------------------------------------------------------- *)

let FINITE_REAL_INTERVAL = `(!a. ~FINITE {x:real | a < x}) /\
   (!a. ~FINITE {x:real | a <= x}) /\
   (!b. ~FINITE {x:real | x < b}) /\
   (!b. ~FINITE {x:real | x <= b}) /\
   (!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a < x /\ x <= b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x <= b} <=> b <= a)`;;

let real_INFINITE = `INFINITE(:real)`;;

(* ------------------------------------------------------------------------- *)
(* Indexing of finite sets and enumeration of subsets of N in order.         *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_INDEX = `!s n. s HAS_SIZE n
         ==> ?f:num->A. (!m. m < n ==> f(m) IN s) /\
                        (!x. x IN s ==> ?!m. m < n /\ (f m = x))`;;

let INFINITE_ENUMERATE = `!s:num->bool.
       INFINITE s
       ==> ?r:num->num. (!m n. m < n ==> r(m) < r(n)) /\
                        IMAGE r (:num) = s`;;

let INFINITE_ENUMERATE_EQ = `!s:num->bool.
     INFINITE s <=> ?r. (!m n:num. m < n ==> r m < r n) /\ IMAGE r (:num) = s`;;

let INFINITE_ENUMERATE_SUBSET = `!s. INFINITE s <=>
       ?f:num->A. (!x. f x IN s) /\ (!x y. f x = f y ==> x = y)`;;

(* ------------------------------------------------------------------------- *)
(* Mapping between finite sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

let set_of_list = new_recursive_definition list_RECURSION
  `(set_of_list ([]:A list) = {}) /\
   (set_of_list (CONS (h:A) t) = h INSERT (set_of_list t))`;;

let list_of_set = new_definition
  `list_of_set s = @l:A list. set_of_list l = s /\ LENGTH l = CARD s`;;

let LIST_OF_SET_PROPERTIES = `!s:A->bool. FINITE(s)
               ==> (set_of_list(list_of_set s) = s) /\
                   (LENGTH(list_of_set s) = CARD s)`;;

let SET_OF_LIST_OF_SET = `!s:A->bool. FINITE(s) ==> (set_of_list(list_of_set s) = s)`;;

let LENGTH_LIST_OF_SET = `!s:A->bool. FINITE(s) ==> (LENGTH(list_of_set s) = CARD s)`;;

let MEM_LIST_OF_SET = `!s:A->bool. FINITE(s) ==> !x. MEM x (list_of_set s) <=> x IN s`;;

let FINITE_SET_OF_LIST = `!l:A list. FINITE(set_of_list l)`;;

let IN_SET_OF_LIST = `!x l:A list. x IN (set_of_list l) <=> MEM x l`;;

let SET_OF_LIST_APPEND = `!l1 l2:A list.
        set_of_list(APPEND l1 l2) = set_of_list(l1) UNION set_of_list(l2)`;;

let SET_OF_LIST_MAP = `!(f:A->B) l. set_of_list(MAP f l) = IMAGE f (set_of_list l)`;;

let SET_OF_LIST_EQ_EMPTY = `!l:A list. set_of_list l = {} <=> l = []`;;

let LIST_OF_SET_EMPTY = `list_of_set {}:A list = []`;;

let LIST_OF_SET_SING = `!a:A. list_of_set {a} = [a]`;;

(* ------------------------------------------------------------------------- *)
(* Mappings from finite set enumerations to lists (no "setification").       *)
(* ------------------------------------------------------------------------- *)

let dest_setenum =
  let fn = splitlist (dest_binary "INSERT") in
  fun tm -> let l,n = fn tm in
            if is_const n && fst(dest_const n) = "EMPTY" then l
            else failwith "dest_setenum: not a finite set enumeration";;

let is_setenum = can dest_setenum;;

let mk_setenum =
  let insert_atm = `(INSERT):A->(A->bool)->(A->bool)`
  and nil_atm = `(EMPTY):A->bool` in
  fun (l,ty) ->
    let insert_tm = inst [ty,aty] insert_atm
    and nil_tm = inst [ty,aty] nil_atm in
    itlist (mk_binop insert_tm) l nil_tm;;

let mk_fset l = mk_setenum(l,type_of(hd l));;

(* ------------------------------------------------------------------------- *)
(* Pairwise property over sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

let pairwise = new_definition
  `pairwise r (s:A->bool) <=> !x y. x IN s /\ y IN s /\ ~(x = y) ==> r x y`;;

let PAIRWISE_EMPTY = `!r:A->A->bool. pairwise r {} <=> T`;;

let PAIRWISE_SING = `!r x:A. pairwise r {x} <=> T`;;

let PAIRWISE_IMP = `!P Q s:A->bool.
        pairwise P s /\
        (!x y. x IN s /\ y IN s /\ P x y /\ ~(x = y) ==> Q x y)
        ==> pairwise Q s`;;

let PAIRWISE_MONO = `!(r:A->A->bool) s t. pairwise r s /\ t SUBSET s ==> pairwise r t`;;

let PAIRWISE_AND = `!R R' s. pairwise R s /\ pairwise R' s <=>
            pairwise (\x y:A. R x y /\ R' x y) s`;;

let PAIRWISE_INSERT = `!r x s.
        pairwise r (x INSERT s) <=>
        (!y:A. y IN s /\ ~(y = x) ==> r x y /\ r y x) /\
        pairwise r s`;;

let PAIRWISE_INSERT_SYMMETRIC = `!r (x:A) s.
        (!y. y IN s ==> (r x y <=> r y x))
        ==> (pairwise r (x INSERT s) <=>
             (!y. y IN s /\ ~(y = x) ==> r x y) /\ pairwise r s)`;;

let PAIRWISE_IMAGE = `!r (f:A->B).
        pairwise r (IMAGE f s) <=>
        pairwise (\x y. ~(f x = f y) ==> r (f x) (f y)) s`;;

let PAIRWISE_UNION = `!R s t. pairwise R (s UNION t) <=>
           pairwise R s /\ pairwise R t /\
           (!x y:A. x IN s DIFF t /\ y IN t DIFF s ==> R x y /\ R y x)`;;

let PAIRWISE_CHAIN_UNIONS = `!R:A->A->bool c.
        (!s. s IN c ==> pairwise R s) /\
        (!s t. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s)
        ==> pairwise R (UNIONS c)`;;

let DIFF_UNIONS_PAIRWISE_DISJOINT = `!s t:(A->bool)->bool.
        pairwise DISJOINT s /\ t SUBSET s
        ==> UNIONS s DIFF UNIONS t = UNIONS(s DIFF t)`;;

let INTER_UNIONS_PAIRWISE_DISJOINT = `!s t:(A->bool)->bool.
        pairwise DISJOINT (s UNION t)
        ==> UNIONS s INTER UNIONS t = UNIONS(s INTER t)`;;

let PSUBSET_UNIONS_PAIRWISE_DISJOINT = `!u v:(A->bool)->bool.
        pairwise DISJOINT v /\ u PSUBSET (v DELETE {})
        ==> UNIONS u PSUBSET UNIONS v`;;

(* ------------------------------------------------------------------------- *)
(* Useful idioms for being a suitable union/intersection of somethings.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("UNION_OF",(20,"right"));;
parse_as_infix("INTERSECTION_OF",(20,"right"));;

let UNION_OF = new_definition
 `P UNION_OF Q =
   \s:A->bool. ?u. P u /\ (!c. c IN u ==> Q c) /\ UNIONS u = s`;;

let INTERSECTION_OF = new_definition
 `P INTERSECTION_OF Q =
   \s:A->bool. ?u. P u /\ (!c. c IN u ==> Q c) /\ INTERS u = s`;;

let UNION_OF_INC = `!P Q s:A->bool. P {s} /\ Q s ==> (P UNION_OF Q) s`;;

let INTERSECTION_OF_INC = `!P Q s:A->bool. P {s} /\ Q s ==> (P INTERSECTION_OF Q) s`;;

let UNION_OF_MONO = `!P Q Q' s:A->bool.
        (P UNION_OF Q) s /\ (!x. Q x ==> Q' x) ==> (P UNION_OF Q') s`;;

let INTERSECTION_OF_MONO = `!P Q Q' s:A->bool.
        (P INTERSECTION_OF Q) s /\ (!x. Q x ==> Q' x)
        ==> (P INTERSECTION_OF Q') s`;;

let FORALL_UNION_OF = `(!s:A->bool. (P UNION_OF Q) s ==> R s) <=>
   (!t. P t /\ (!c. c IN t ==> Q c) ==> R(UNIONS t))`;;

let FORALL_INTERSECTION_OF = `(!s:A->bool. (P INTERSECTION_OF Q) s ==> R s) <=>
   (!t. P t /\ (!c. c IN t ==> Q c) ==> R(INTERS t))`;;

let UNION_OF_EMPTY = `!P Q:(A->bool)->bool. P {} ==> (P UNION_OF Q) {}`;;

let INTERSECTION_OF_EMPTY = `!P Q:(A->bool)->bool. P {} ==> (P INTERSECTION_OF Q) UNIV`;;

(* ------------------------------------------------------------------------- *)
(* The ARBITRARY and FINITE cases of UNION_OF / INTERSECTION_OF              *)
(* ------------------------------------------------------------------------- *)

let ARBITRARY = new_definition
 `ARBITRARY (s:(A->bool)->bool) <=> T`;;

let ARBITRARY_UNION_OF_ALT = `!B s:A->bool.
        (ARBITRARY UNION_OF B) s <=>
        !x. x IN s ==>  ?u. u IN B /\ x IN u /\ u SUBSET s`;;

let ARBITRARY_UNION_OF_EMPTY = `!P:(A->bool)->bool. (ARBITRARY UNION_OF P) {}`;;

let ARBITRARY_INTERSECTION_OF_EMPTY = `!P:(A->bool)->bool. (ARBITRARY INTERSECTION_OF P) UNIV`;;

let ARBITRARY_UNION_OF_INC = `!P s:A->bool. P s ==> (ARBITRARY UNION_OF P) s`;;

let ARBITRARY_INTERSECTION_OF_INC = `!P s:A->bool. P s ==> (ARBITRARY INTERSECTION_OF P) s`;;

let ARBITRARY_UNION_OF_COMPLEMENT = `!P s. (ARBITRARY UNION_OF P) s <=>
         (ARBITRARY INTERSECTION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`;;

let ARBITRARY_INTERSECTION_OF_COMPLEMENT = `!P s. (ARBITRARY INTERSECTION_OF P) s <=>
         (ARBITRARY UNION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`;;

let ARBITRARY_UNION_OF_IDEMPOT = `!P:(A->bool)->bool.
        ARBITRARY UNION_OF ARBITRARY UNION_OF P = ARBITRARY UNION_OF P`;;

let ARBITRARY_INTERSECTION_OF_IDEMPOT = `!P:(A->bool)->bool.
        ARBITRARY INTERSECTION_OF ARBITRARY INTERSECTION_OF P =
        ARBITRARY INTERSECTION_OF P`;;

let ARBITRARY_UNION_OF_UNIONS = `!P u:(A->bool)->bool.
        (!s. s IN u ==> (ARBITRARY UNION_OF P) s)
        ==> (ARBITRARY UNION_OF P) (UNIONS u)`;;

let ARBITRARY_UNION_OF_UNION = `!P s t:A->bool.
        (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
        ==> (ARBITRARY UNION_OF P) (s UNION t)`;;

let ARBITRARY_INTERSECTION_OF_INTERS = `!P u:(A->bool)->bool.
        (!s. s IN u ==> (ARBITRARY INTERSECTION_OF P) s)
        ==> (ARBITRARY INTERSECTION_OF P) (INTERS u)`;;

let ARBITRARY_INTERSECTION_OF_INTER = `!P s t:A->bool.
        (ARBITRARY INTERSECTION_OF P) s /\ (ARBITRARY INTERSECTION_OF P) t
        ==> (ARBITRARY INTERSECTION_OF P) (s INTER t)`;;

let ARBITRARY_UNION_OF_INTER_EQ = `!P:(A->bool)->bool.
        (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
               ==> (ARBITRARY UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (ARBITRARY UNION_OF P) (s INTER t))`;;

let ARBITRARY_UNION_OF_INTER = `!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
                   ==> (ARBITRARY UNION_OF P) (s INTER t))`;;

let ARBITRARY_INTERSECTION_OF_UNION_EQ = `!P:(A->bool)->bool.
        (!s t. (ARBITRARY INTERSECTION_OF P) s /\
               (ARBITRARY INTERSECTION_OF P) t
               ==> (ARBITRARY INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))`;;

let ARBITRARY_INTERSECTION_OF_UNION = `!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (ARBITRARY INTERSECTION_OF P) s /\
                   (ARBITRARY INTERSECTION_OF P) t
                   ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))`;;

let FINITE_UNION_OF_EMPTY = `!P:(A->bool)->bool. (FINITE UNION_OF P) {}`;;

let FINITE_INTERSECTION_OF_EMPTY = `!P:(A->bool)->bool. (FINITE INTERSECTION_OF P) UNIV`;;

let FINITE_UNION_OF_INC = `!P s:A->bool. P s ==> (FINITE UNION_OF P) s`;;

let FINITE_INTERSECTION_OF_INC = `!P s:A->bool. P s ==> (FINITE INTERSECTION_OF P) s`;;

let FINITE_UNION_OF_COMPLEMENT = `!P s. (FINITE UNION_OF P) s <=>
         (FINITE INTERSECTION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`;;

let FINITE_INTERSECTION_OF_COMPLEMENT = `!P s. (FINITE INTERSECTION_OF P) s <=>
         (FINITE UNION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`;;

let FINITE_UNION_OF_IDEMPOT = `!P:(A->bool)->bool.
        FINITE UNION_OF FINITE UNION_OF P = FINITE UNION_OF P`;;

let FINITE_INTERSECTION_OF_IDEMPOT = `!P:(A->bool)->bool.
        FINITE INTERSECTION_OF FINITE INTERSECTION_OF P =
        FINITE INTERSECTION_OF P`;;

let FINITE_UNION_OF_UNIONS = `!P u:(A->bool)->bool.
        FINITE u /\ (!s. s IN u ==> (FINITE UNION_OF P) s)
        ==> (FINITE UNION_OF P) (UNIONS u)`;;

let FINITE_UNION_OF_UNION = `!P s t:A->bool.
        (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
        ==> (FINITE UNION_OF P) (s UNION t)`;;

let FINITE_INTERSECTION_OF_INTERS = `!P u:(A->bool)->bool.
        FINITE u /\ (!s. s IN u ==> (FINITE INTERSECTION_OF P) s)
        ==> (FINITE INTERSECTION_OF P) (INTERS u)`;;

let FINITE_INTERSECTION_OF_INTER = `!P s t:A->bool.
        (FINITE INTERSECTION_OF P) s /\ (FINITE INTERSECTION_OF P) t
        ==> (FINITE INTERSECTION_OF P) (s INTER t)`;;

let FINITE_UNION_OF_INTER_EQ = `!P:(A->bool)->bool.
        (!s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
                   ==> (FINITE UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (FINITE UNION_OF P) (s INTER t))`;;

let FINITE_UNION_OF_INTER = `!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
                   ==> (FINITE UNION_OF P) (s INTER t))`;;

let FINITE_INTERSECTION_OF_UNION_EQ = `!P:(A->bool)->bool.
        (!s t. (FINITE INTERSECTION_OF P) s /\
               (FINITE INTERSECTION_OF P) t
               ==> (FINITE INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (FINITE INTERSECTION_OF P) (s UNION t))`;;

let FINITE_INTERSECTION_OF_UNION = `!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (FINITE INTERSECTION_OF P) s /\
                   (FINITE INTERSECTION_OF P) t
                   ==> (FINITE INTERSECTION_OF P) (s UNION t))`;;

(* ------------------------------------------------------------------------- *)
(* Some additional properties of "set_of_list".                              *)
(* ------------------------------------------------------------------------- *)

let CARD_SET_OF_LIST_LE = `!l:A list. CARD(set_of_list l) <= LENGTH l`;;

let HAS_SIZE_SET_OF_LIST = `!l. (set_of_list l) HAS_SIZE (LENGTH l) <=> PAIRWISE (\x y:A. ~(x = y)) l`;;

(* ------------------------------------------------------------------------- *)
(* Classic result on function of finite set into itself.                     *)
(* ------------------------------------------------------------------------- *)

let SURJECTIVE_IFF_INJECTIVE_GEN = `!s t f:A->B.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\ (IMAGE f s) SUBSET t
        ==> ((!y. y IN t ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`;;

let SURJECTIVE_IFF_INJECTIVE = `!s f:A->A.
        FINITE s /\ (IMAGE f s) SUBSET s
        ==> ((!y. y IN s ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`;;

let IMAGE_IMP_INJECTIVE_GEN = `!s t f:A->B.
        FINITE s /\ (CARD s = CARD t) /\ (IMAGE f s = t)
        ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`;;

let IMAGE_IMP_INJECTIVE = `!s f:A->A.
        FINITE s /\ IMAGE f s = s
        ==> !x y. x IN s /\ y IN s /\ f x = f y ==> x = y`;;

let HAS_SIZE_IMAGE_INJ_RESTRICT = `!(f:A->B) s t P n.
      FINITE s /\ FINITE t /\ CARD s = CARD t /\
      IMAGE f s SUBSET t /\
      (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
      {x | x IN s /\ P(f x)} HAS_SIZE n
      ==> {x | x IN t /\ P x} HAS_SIZE n`;;

(* ------------------------------------------------------------------------- *)
(* Converse relation between cardinality and injection.                      *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_INJ = `!s t. FINITE s /\ FINITE t /\ CARD s <= CARD t
   ==> ?f:A->B. (IMAGE f s) SUBSET t /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`;;

(* ------------------------------------------------------------------------- *)
(* Occasionally handy rewrites.                                              *)
(* ------------------------------------------------------------------------- *)

let FORALL_IN_CLAUSES = `(!P. (!x:A. x IN {} ==> P x) <=> T) /\
   (!P a s. (!x:A. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x))`;;

let EXISTS_IN_CLAUSES = `(!P. (?x:A. x IN {} /\ P x) <=> F) /\
   (!P a s. (?x:A. x IN (a INSERT s) /\ P x) <=> P a \/ (?x. x IN s /\ P x))`;;

(* ------------------------------------------------------------------------- *)
(* Injectivity and surjectivity of image and preimage under a function.      *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_ON_IMAGE = `!f:A->B u.
    (!s t. s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t ==> s = t) <=>
    (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)`;;

let INJECTIVE_IMAGE = `!f:A->B.
    (!s t. IMAGE f s = IMAGE f t ==> s = t) <=> (!x y. f x = f y ==> x = y)`;;

let SURJECTIVE_ON_IMAGE = `!f:A->B u v.
        (!t. t SUBSET v ==> ?s. s SUBSET u /\ IMAGE f s = t) <=>
        (!y. y IN v ==> ?x. x IN u /\ f x = y)`;;

let SURJECTIVE_IMAGE = `!f:A->B. (!t. ?s. IMAGE f s = t) <=> (!y. ?x. f x = y)`;;

let INJECTIVE_ON_PREIMAGE = `!f:A->B s u.
        (!t t'. t SUBSET u /\ t' SUBSET u /\
                {x | x IN s /\ f x IN t} = {x | x IN s /\ f x IN t'}
                ==> t = t') <=>
        u SUBSET IMAGE f s`;;

let SURJECTIVE_ON_PREIMAGE = `!f:A->B s u.
        (!k. k SUBSET s
             ==> ?t. t SUBSET u /\ {x | x IN s /\ f x IN t} = k) <=>
        IMAGE f s SUBSET u /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`;;

let INJECTIVE_PREIMAGE = `!f:A->B.
        (!t t'. {x | f x IN t} = {x | f x IN t'} ==> t = t') <=>
        IMAGE f UNIV = UNIV`;;

let SURJECTIVE_PREIMAGE = `!f:A->B. (!k. ?t. {x | f x IN t} = k) <=> (!x y. f x = f y ==> x = y)`;;

(* ------------------------------------------------------------------------- *)
(* Existence of bijections between two finite sets of same size.             *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_BIJECTION = `!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B. (!x. x IN s ==> f(x) IN t) /\
                (!y. y IN t ==> ?x. x IN s /\ f x = y) /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`;;

let CARD_EQ_BIJECTIONS = `!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B g. (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
                  (!y. y IN t ==> g(y) IN s /\ f(g y) = y)`;;

let CARD_EQ_BIJECTIONS_SPECIAL = `!s t (a:A) (b:B).
         FINITE s /\ FINITE t /\ CARD s = CARD t /\ a IN s /\ b IN t
         ==> ?f g. f a = b /\ g b = a /\
                   (!x. x IN s ==> f x IN t /\ g (f x) = x) /\
                   (!y. y IN t ==> g y IN s /\ f (g y) = y)`;;

let BIJECTIONS_HAS_SIZE = `!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y) /\
        s HAS_SIZE n
        ==> t HAS_SIZE n`;;

let BIJECTIONS_HAS_SIZE_EQ = `!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> !n. s HAS_SIZE n <=> t HAS_SIZE n`;;

let BIJECTIONS_CARD_EQ = `!s t f:A->B g.
        (FINITE s \/ FINITE t) /\
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> CARD s = CARD t`;;

(* ------------------------------------------------------------------------- *)
(* Transitive relation with finitely many predecessors is wellfounded.       *)
(* ------------------------------------------------------------------------- *)

let WF_FINITE = `!(<<). (!x. ~(x << x)) /\ (!x y z. x << y /\ y << z ==> x << z) /\
          (!x:A. FINITE {y | y << x})
          ==> WF(<<)`;;

let WF_PSUBSET = `!s:A->bool. FINITE s ==> WF (\t1 t2. t1 PSUBSET t2 /\ t2 SUBSET s)`;;

(* ------------------------------------------------------------------------- *)
(* Cardinal comparisons (more theory in Library/card.ml)                     *)
(* ------------------------------------------------------------------------- *)

let le_c = new_definition
  `s <=_c t <=>
   ?f:A->B. (!x. x IN s ==> f(x) IN t) /\
            (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y)`;;

let lt_c = new_definition
  `(s:A->bool) <_c (t:B->bool) <=> s <=_c t /\ ~(t <=_c s)`;;

let eq_c = new_definition
  `(s:A->bool) =_c (t:B->bool) <=>
   ?f. (!x. x IN s ==> f(x) IN t) /\
       !y. y IN t ==> ?!x. x IN s /\ (f x = y)`;;

let ge_c = new_definition
 `(s:A->bool) >=_c (t:B->bool) <=> t <=_c s`;;

let gt_c = new_definition
 `(s:A->bool) >_c (t:B->bool) <=> t <_c s`;;

let LE_C = `!s t. s <=_c t <=> ?g:A->B. !x. x IN s ==> ?y. y IN t /\ g y = x`;;

let GE_C = `!s t. s >=_c t <=> ?f:A->B. !y. y IN t ==> ?x. x IN s /\ (y = f x)`;;

let COUNTABLE = new_definition
  `COUNTABLE (t:A->bool) <=> (:num) >=_c t`;;

(* ------------------------------------------------------------------------- *)
(* Supremum and infimum.                                                     *)
(* ------------------------------------------------------------------------- *)

let sup = new_definition
  `sup s = @a:real. (!x. x IN s ==> x <= a) /\
                    !b. (!x. x IN s ==> x <= b) ==> a <= b`;;

let SUP_EQ = `!s t. (!b. (!x. x IN s ==> x <= b) <=> (!x. x IN t ==> x <= b))
         ==> sup s = sup t`;;

let SUP = `!s. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)
       ==> (!x. x IN s ==> x <= sup s) /\
           !b. (!x. x IN s ==> x <= b) ==> sup s <= b`;;

let SUP_FINITE_LEMMA = `!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> x <= b`;;

let SUP_FINITE = `!s. FINITE s /\ ~(s = {}) ==> (sup s) IN s /\ !x. x IN s ==> x <= sup s`;;

let REAL_LE_SUP_FINITE = `!s a. FINITE s /\ ~(s = {}) ==> (a <= sup s <=> ?x. x IN s /\ a <= x)`;;

let REAL_SUP_LE_FINITE = `!s a. FINITE s /\ ~(s = {}) ==> (sup s <= a <=> !x. x IN s ==> x <= a)`;;

let REAL_LT_SUP_FINITE = `!s a. FINITE s /\ ~(s = {}) ==> (a < sup s <=> ?x. x IN s /\ a < x)`;;

let REAL_SUP_LT_FINITE = `!s a. FINITE s /\ ~(s = {}) ==> (sup s < a <=> !x. x IN s ==> x < a)`;;

let REAL_SUP_UNIQUE = `!s b. (!x. x IN s ==> x <= b) /\
         (!b'. b' < b ==> ?x. x IN s /\ b' < x)
         ==> sup s = b`;;

let REAL_SUP_LE = `!b. ~(s = {}) /\ (!x. x IN s ==> x <= b) ==> sup s <= b`;;

let REAL_SUP_LE_SUBSET = `!s t. ~(s = {}) /\ s SUBSET t /\ (?b. !x. x IN t ==> x <= b)
         ==> sup s <= sup t`;;

let REAL_SUP_BOUNDS = `!s a b. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= sup s /\ sup s <= b`;;

let REAL_ABS_SUP_LE = `!s a. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(sup s) <= a`;;

let REAL_SUP_ASCLOSE = `!s l e. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(sup s - l) <= e`;;

let SUP_UNIQUE_FINITE = `!s. FINITE s /\ ~(s = {})
       ==> (sup s = a <=> a IN s /\ !y. y IN s ==> y <= a)`;;

let SUP_INSERT_FINITE = `!x s. FINITE s ==> sup(x INSERT s) = if s = {} then x else max x (sup s)`;;

let SUP_SING = `!a. sup {a} = a`;;

let SUP_INSERT_INSERT = `!a b s. sup (b INSERT a INSERT s) = sup (max a b INSERT s)`;;

let REAL_LE_SUP = `!s a b y. y IN s /\ a <= y /\ (!x. x IN s ==> x <= b) ==> a <= sup s`;;

let REAL_SUP_LE_EQ = `!s y. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)
         ==> (sup s <= y <=> !x. x IN s ==> x <= y)`;;

let SUP_UNIQUE = `!s b. (!c. (!x. x IN s ==> x <= c) <=> b <= c) ==> sup s = b`;;

let SUP_UNION = `!s t. ~(s = {}) /\ ~(t = {}) /\
         (?b. !x. x IN s ==> x <= b) /\ (?c. !x. x IN t ==> x <= c)
         ==> sup(s UNION t) = max (sup s) (sup t)`;;

let ELEMENT_LE_SUP = `!s a. (?b. !x. x IN s ==> x <= b) /\ a IN s ==> a <= sup s`;;

let SUP_APPROACH = `!s c. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b) /\ c < sup s
         ==> ?x. x IN s /\ c < x`;;

let REAL_MAX_SUP = `!x y. max x y = sup {x,y}`;;

let inf = new_definition
  `inf s = @a:real. (!x. x IN s ==> a <= x) /\
                    !b. (!x. x IN s ==> b <= x) ==> b <= a`;;

let INF_EQ = `!s t. (!a. (!x. x IN s ==> a <= x) <=> (!x. x IN t ==> a <= x))
         ==> inf s = inf t`;;

let INF = `!s. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)
       ==> (!x. x IN s ==> inf s <= x) /\
           !b. (!x. x IN s ==> b <= x) ==> b <= inf s`;;

let INF_FINITE_LEMMA = `!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> b <= x`;;

let INF_FINITE = `!s. FINITE s /\ ~(s = {}) ==> (inf s) IN s /\ !x. x IN s ==> inf s <= x`;;

let REAL_LE_INF_FINITE = `!s a. FINITE s /\ ~(s = {}) ==> (a <= inf s <=> !x. x IN s ==> a <= x)`;;

let REAL_INF_LE_FINITE = `!s a. FINITE s /\ ~(s = {}) ==> (inf s <= a <=> ?x. x IN s /\ x <= a)`;;

let REAL_LT_INF_FINITE = `!s a. FINITE s /\ ~(s = {}) ==> (a < inf s <=> !x. x IN s ==> a < x)`;;

let REAL_INF_LT_FINITE = `!s a. FINITE s /\ ~(s = {}) ==> (inf s < a <=> ?x. x IN s /\ x < a)`;;

let REAL_INF_UNIQUE = `!s b. (!x. x IN s ==> b <= x) /\
         (!b'. b < b' ==> ?x. x IN s /\ x < b')
         ==> inf s = b`;;

let REAL_LE_INF = `!b. ~(s = {}) /\ (!x. x IN s ==> b <= x) ==> b <= inf s`;;

let REAL_LE_INF_SUBSET = `!s t. ~(t = {}) /\ t SUBSET s /\ (?b. !x. x IN s ==> b <= x)
         ==> inf s <= inf t`;;

let REAL_INF_BOUNDS = `!s a b. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= inf s /\ inf s <= b`;;

let REAL_ABS_INF_LE = `!s a. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(inf s) <= a`;;

let REAL_INF_ASCLOSE = `!s l e. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(inf s - l) <= e`;;

let INF_UNIQUE_FINITE = `!s. FINITE s /\ ~(s = {})
       ==> (inf s = a <=> a IN s /\ !y. y IN s ==> a <= y)`;;

let INF_INSERT_FINITE = `!x s. FINITE s ==> inf(x INSERT s) = if s = {} then x else min x (inf s)`;;

let INF_SING = `!a. inf {a} = a`;;

let INF_INSERT_INSERT = `!a b s. inf (b INSERT a INSERT s) = inf (min a b INSERT s)`;;

let REAL_SUP_EQ_INF = `!s. ~(s = {}) /\ (?B. !x. x IN s ==> abs(x) <= B)
       ==> (sup s = inf s <=> ?a. s = {a})`;;

let REAL_INF_LE = `!s a b y. y IN s /\ y <= b /\ (!x. x IN s ==> a <= x) ==> inf s <= b`;;

let REAL_LE_INF_EQ = `!s y. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)
         ==> (y <= inf s <=> !x. x IN s ==> y <= x)`;;

let INF_UNIQUE = `!s b. (!c. (!x. x IN s ==> c <= x) <=> c <= b) ==> inf s = b`;;

let INF_UNION = `!s t. ~(s = {}) /\ ~(t = {}) /\
         (?b. !x. x IN s ==> b <= x) /\ (?c. !x. x IN t ==> c <= x)
         ==> inf(s UNION t) = min (inf s) (inf t)`;;

let INF_LE_ELEMENT = `!s a. (?b. !x. x IN s ==> b <= x) /\ a IN s ==> inf s <= a`;;

let INF_APPROACH = `!s c. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x) /\ inf s < c
         ==> ?x. x IN s /\ x < c`;;

let REAL_MIN_INF = `!x y. min x y = inf {x,y}`;;

(* ------------------------------------------------------------------------- *)
(* Relational counterparts of sup and inf.                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("has_inf",(12,"right"));;
parse_as_infix ("has_sup",(12,"right"));;

let has_inf = new_definition
  `s has_inf b <=> (!c. (!x:real. x IN s ==> c <= x) <=> c <= b)`;;

let has_sup = new_definition
  `s has_sup b <=> (!c. (!x:real. x IN s ==> x <= c) <=> b <= c)`;;

let HAS_INF_LBOUND = `!s b x. s has_inf b /\ x IN s ==> b <= x`;;

let HAS_SUP_UBOUND = `!s b x. s has_sup b /\ x IN s ==> x <= b`;;

let HAS_INF_INF = `!s l. s has_inf l <=>
         ~(s = {}) /\
         (?b. !x. x IN s ==> b <= x) /\
         inf s = l`;;

let HAS_SUP_SUP = `!s l. s has_sup l <=>
         ~(s = {}) /\
         (?b. !x. x IN s ==> x <= b) /\
         sup s = l`;;

let INF_EXISTS = `!s. (?l. s has_inf l) <=> ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)`;;

let SUP_EXISTS = `!s. (?l. s has_sup l) <=> ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)`;;

let HAS_INF_APPROACH = `!s l c. s has_inf l /\ l < c ==> ?x. x IN s /\ x < c`;;

let HAS_SUP_APPROACH = `!s l c. s has_sup l /\ c < l ==> ?x. x IN s /\ c < x`;;

let HAS_INF = `!s l. s has_inf l <=>
         ~(s = {}) /\
         (!x. x IN s ==> l <= x) /\
         (!c. l < c ==> ?x. x IN s /\ x < c)`;;

let HAS_SUP = `!s l. s has_sup l <=>
         ~(s = {}) /\
         (!x. x IN s ==> x <= l) /\
         (!c. c < l ==> ?x. x IN s /\ c < x)`;;

let HAS_INF_LE = `!s t l m. s has_inf l /\ t has_inf m /\
             (!y. y IN t ==> ?x. x IN s /\ x <= y)
             ==> l <= m`;;

let HAS_SUP_LE = `!s t l m. s has_sup l /\ t has_sup m /\
             (!y. y IN t ==> ?x. x IN s /\ y <= x)
             ==> m <= l`;;

(* ------------------------------------------------------------------------- *)
(* Inductive definition of sets, by reducing them to inductive relations.    *)
(* ------------------------------------------------------------------------- *)

let new_inductive_set =
  let const_of_var v = mk_mconst(name_of v,type_of v) in
  let comb_all =
    let rec f (n:int) (tm:term) : hol_type list -> term = function
      | [] -> tm
      | ty::tys ->
          let v = variant (variables tm) (mk_var("x"^string_of_int n,ty)) in
          f (n+1) (mk_comb(tm,v)) tys in
    fun tm -> let tys = fst (splitlist dest_fun_ty (type_of tm)) in
              f 0 tm tys in
  let mk_eqin = REWR_CONV (GSYM IN) o comb_all in
  let transf conv = rhs o concl o conv in
  let remove_in_conv ptm : conv =
    let rconv = REWR_CONV(SYM(mk_eqin ptm)) in
    fun tm -> let htm = fst(strip_comb(snd(dest_binary "IN" tm))) in
              if htm = ptm then rconv tm else fail() in
  let remove_in_transf =
    transf o ONCE_DEPTH_CONV o FIRST_CONV o map remove_in_conv in
  let rule_head tm =
    let tm = snd(strip_forall tm) in
    let tm = snd(splitlist(dest_binop `(==>)`) tm) in
    let tm = snd(dest_binary "IN" tm) in
    fst(strip_comb tm) in
  let find_pvars = setify o map rule_head o binops `(/\)` in
  fun tm ->
    let pvars = find_pvars tm in
    let dtm = remove_in_transf pvars tm in
    let th_rules, th_induct, th_cases = new_inductive_definition dtm in
    let insert_in_rule = REWRITE_RULE(map (mk_eqin o const_of_var) pvars) in
    insert_in_rule th_rules,
    insert_in_rule th_induct,
    insert_in_rule th_cases;;
