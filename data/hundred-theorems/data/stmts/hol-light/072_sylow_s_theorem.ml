(* ========================================================================= *)
(* Simple formulation of group theory with a type of "(A)group".             *)
(* ========================================================================= *)

needs "Library/frag.ml";;       (* Used eventually for free Abelian groups   *)
needs "Library/card.ml";;       (* Need cardinal arithmetic in a few places  *)
needs "Library/prime.ml";;      (* For elementary number-theoretic lemmas    *)

(* ------------------------------------------------------------------------- *)
(* Basic type of groups.                                                     *)
(* ------------------------------------------------------------------------- *)

let group_tybij =
  let eth = `?s (z:A) n a.
          z IN s /\
          (!x. x IN s ==> n x IN s) /\
          (!x y. x IN s /\ y IN s ==> a x y IN s) /\
          (!x y z. x IN s /\ y IN s /\ z IN s
                   ==> a x (a y z) = a (a x y) z) /\
          (!x. x IN s ==> a z x = x /\ a x z = x) /\
          (!x. x IN s ==> a (n x) x = z /\ a x (n x) = z)`;;

let group_carrier = new_definition
 `(group_carrier:(A)group->A->bool) = \g. FST(group_operations g)`;;

let group_id = new_definition
 `(group_id:(A)group->A) = \g. FST(SND(group_operations g))`;;

let group_inv = new_definition
 `(group_inv:(A)group->A->A) = \g. FST(SND(SND(group_operations g)))`;;

let group_mul = new_definition
 `(group_mul:(A)group->A->A->A) = \g. SND(SND(SND(group_operations g)))`;;

let ([GROUP_ID; GROUP_INV; GROUP_MUL; GROUP_MUL_ASSOC;
      GROUP_MUL_LID; GROUP_MUL_RID; GROUP_MUL_LINV; GROUP_MUL_RINV] as
     GROUP_PROPERTIES) = (CONJUNCTS o prove)
 (`(!G:A group. group_id G IN group_carrier G) /\
   (!G x:A. x IN group_carrier G ==> group_inv G x IN group_carrier G) /\
   (!G x y:A. x IN group_carrier G /\ y IN group_carrier G
              ==> group_mul G x y IN group_carrier G) /\
   (!G x y z:A. x IN group_carrier G /\
                y IN group_carrier G /\
                z IN group_carrier G
                ==> group_mul G x (group_mul G y z) =
                    group_mul G (group_mul G x y) z) /\
   (!G x:A. x IN group_carrier G ==> group_mul G (group_id G) x = x) /\
   (!G x:A. x IN group_carrier G ==> group_mul G x (group_id G) = x) /\
   (!G x:A. x IN group_carrier G
            ==> group_mul G (group_inv G x) x = group_id G) /\
   (!G x:A. x IN group_carrier G
            ==> group_mul G x(group_inv G x) = group_id G)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MP_TAC(SPEC `G:A group` (MATCH_MP(MESON[]
   `(!a. mk(dest a) = a) /\ (!r. P r <=> dest(mk r) = r)
    ==> !a. P(dest a)`) group_tybij)) THEN
  REWRITE_TAC[group_carrier; group_id; group_inv; group_mul] THEN
  SIMP_TAC[]);;

let GROUPS_EQ = `!G H:A group.
        G = H <=>
        group_carrier G = group_carrier H /\
        group_id G = group_id H /\
        group_inv G = group_inv H /\
        group_mul G = group_mul H`;;

let GROUP_CARRIER_NONEMPTY = `!G:A group. ~(group_carrier G = {})`;;

(* ------------------------------------------------------------------------- *)
(* The trivial group on a given object.                                      *)
(* ------------------------------------------------------------------------- *)

let singleton_group = new_definition
 `singleton_group (a:A) = group({a},a,(\x. a),(\x y. a))`;;

let SINGLETON_GROUP = `(!a:A. group_carrier(singleton_group a) = {a}) /\
   (!a:A. group_id(singleton_group a) = a) /\
   (!a:A. group_inv(singleton_group a) = \x. a) /\
   (!a:A. group_mul(singleton_group a) = \x y. a)`;;

let trivial_group = new_definition
 `trivial_group G <=> group_carrier G = {group_id G}`;;

let TRIVIAL_IMP_FINITE_GROUP = `!G:A group. trivial_group G ==> FINITE(group_carrier G)`;;

let TRIVIAL_GROUP_SINGLETON_GROUP = `!a:A. trivial_group(singleton_group a)`;;

let FINITE_SINGLETON_GROUP = `!a:A. FINITE(group_carrier(singleton_group a))`;;

let TRIVIAL_GROUP_SUBSET = `!G:A group. trivial_group G <=> group_carrier G SUBSET {group_id G}`;;

let TRIVIAL_GROUP = `!G:A group. trivial_group G <=> ?a. group_carrier G = {a}`;;

let TRIVIAL_GROUP_ALT = `!G:A group. trivial_group G <=> ?a. group_carrier G SUBSET {a}`;;

let TRIVIAL_GROUP_HAS_SIZE_1 = `!G:A group. trivial_group G <=> group_carrier(G) HAS_SIZE 1`;;

let GROUP_CARRIER_HAS_SIZE_1 = `!G:A group. group_carrier(G) HAS_SIZE 1 <=> trivial_group G`;;

(* ------------------------------------------------------------------------- *)
(* Opposite group (mainly just to avoid some duplicated variant proofs).     *)
(* ------------------------------------------------------------------------- *)

let opposite_group = new_definition
 `opposite_group(G:A group) =
        group(group_carrier G,group_id G,group_inv G,
              \x y. group_mul G y x)`;;

let OPPOSITE_GROUP = `!G:A group.
        group_carrier(opposite_group G) = group_carrier G /\
        group_id(opposite_group G) = group_id G /\
        group_inv(opposite_group G) = group_inv G /\
        group_mul(opposite_group G) = \x y. group_mul G y x`;;

let OPPOSITE_OPPOSITE_GROUP = `!G:A group. opposite_group (opposite_group G) = G`;;

let OPPOSITE_GROUP_INV = `!G x:A. group_inv(opposite_group G) x = group_inv G x`;;

let OPPOSITE_GROUP_MUL = `!G x y:A. group_mul(opposite_group G) x y = group_mul G y x`;;

let OPPOSITE_SINGLETON_GROUP = `!a:A. opposite_group(singleton_group a) = singleton_group a`;;

let TRIVIAL_OPPOSITE_GROUP = `!G:A group. trivial_group(opposite_group G) <=> trivial_group G`;;

let FINITE_OPPOSITE_GROUP = `!G:A group. FINITE(group_carrier(opposite_group G)) <=>
               FINITE(group_carrier G)`;;

(* ------------------------------------------------------------------------- *)
(* Derived operations and derived properties, including separate "powers"    *)
(* for natural number (group_pow) and integer (group_zpow) indices.          *)
(* ------------------------------------------------------------------------- *)

let group_div = new_definition
 `group_div G x y = group_mul G x (group_inv G y)`;;

let GROUP_DIV = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_div G x y) IN group_carrier G`;;

let GROUP_MUL_LCANCEL = `!G x y z:A.
        x IN group_carrier G /\ y IN group_carrier G /\ z IN group_carrier G
        ==> (group_mul G x y = group_mul G x z <=> y = z)`;;

let GROUP_MUL_LCANCEL_IMP = `!G x y z:A.
        x IN group_carrier G /\ y IN group_carrier G /\ z IN group_carrier G /\
        group_mul G x y = group_mul G x z
        ==> y = z`;;

let GROUP_MUL_RCANCEL = `!G x y z:A.
        x IN group_carrier G /\ y IN group_carrier G /\ z IN group_carrier G
        ==> (group_mul G x z = group_mul G y z <=> x = y)`;;

let GROUP_MUL_RCANCEL_IMP = `!G x y z:A.
        x IN group_carrier G /\ y IN group_carrier G /\ z IN group_carrier G /\
        group_mul G x z = group_mul G y z
        ==> x = y`;;

let GROUP_LID_UNIQUE = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\ group_mul G x y = y
        ==> x = group_id G`;;

let GROUP_RID_UNIQUE = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\ group_mul G x y = x
        ==> y = group_id G`;;

let GROUP_LID_EQ = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_mul G x y = y <=> x = group_id G)`;;

let GROUP_RID_EQ = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_mul G x y = x <=> y = group_id G)`;;

let GROUP_LINV_UNIQUE = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_id G
        ==> group_inv G x = y`;;

let GROUP_RINV_UNIQUE = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_id G
        ==> group_inv G y = x`;;

let GROUP_LINV_EQ = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_inv G x = y <=> group_mul G x y = group_id G)`;;

let GROUP_RINV_EQ = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_inv G x = y <=> group_mul G y x = group_id G)`;;

let GROUP_MUL_EQ_ID = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_mul G x y = group_id G <=> group_mul G y x = group_id G)`;;

let GROUP_INV_INV = `!G x:A. x IN group_carrier G ==> group_inv G (group_inv G x) = x`;;

let GROUP_INV_ID = `!G:A group. group_inv G (group_id G) = group_id G`;;

let GROUP_INV_EQ_ID = `!G x:A.
        x IN group_carrier G
        ==> (group_inv G x = group_id G <=> x = group_id G)`;;

let GROUP_INV_MUL = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> group_inv G (group_mul G x y) =
            group_mul G (group_inv G y) (group_inv G x)`;;

let GROUP_INV_EQ = `!G x y:A. x IN group_carrier G /\ y IN group_carrier G
             ==> (group_inv G x = group_inv G y <=> x = y)`;;

let GROUP_DIV_REFL = `!G x:A. x IN group_carrier G ==> group_div G x x = group_id G`;;

let GROUP_DIV_EQ_ID = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_div G x y = group_id G <=> x = y)`;;

let GROUP_COMMUTES_INV = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==>  group_mul G (group_inv G x) y = group_mul G y (group_inv G x)`;;

let GROUP_COMMUTES_INV_EQ = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_mul G (group_inv G x) y = group_mul G y (group_inv G x) <=>
             group_mul G x y = group_mul G y x)`;;

let GROUP_COMMUTES_MUL = `!G x y z:A.
        x IN group_carrier G /\
        y IN group_carrier G /\
        z IN group_carrier G /\
        group_mul G x z = group_mul G z x /\
        group_mul G y z = group_mul G z y
        ==> group_mul G (group_mul G x y) z = group_mul G z (group_mul G x y)`;;

let FORALL_IN_GROUP_CARRIER_INV = `!(P:A->bool) G.
        (!x. x IN group_carrier G ==> P(group_inv G x)) <=>
        (!x. x IN group_carrier G ==> P x)`;;

let EXISTS_IN_GROUP_CARRIER_INV = `!P G:A group.
        (?x. x IN group_carrier G /\ P(group_inv G x)) <=>
        (?x. x IN group_carrier G /\ P x)`;;

let group_pow = new_recursive_definition num_RECURSION
 `group_pow G x 0 = group_id G /\
  group_pow G x (SUC n) = group_mul G x (group_pow G x n)`;;

let GROUP_POW = `!G (x:A) n. x IN group_carrier G ==> group_pow G x n IN group_carrier G`;;

let GROUP_POW_0 = `!G (x:A). group_pow G x 0 = group_id G`;;

let GROUP_POW_1 = `!G x:A. x IN group_carrier G ==> group_pow G x 1 = x`;;

let GROUP_POW_2 = `!G x:A. x IN group_carrier G ==> group_pow G x 2 = group_mul G x x`;;

let GROUP_POW_ID = `!n. group_pow G (group_id G) n = group_id G`;;

let GROUP_POW_ADD = `!G (x:A) m n.
        x IN group_carrier G
        ==> group_pow G x (m + n) =
            group_mul G (group_pow G x m) (group_pow G x n)`;;

let GROUP_POW_SUB = `!G (x:A) m n.
        x IN group_carrier G /\ n <= m
        ==> group_pow G x (m - n) =
            group_div G (group_pow G x m) (group_pow G x n)`;;

let GROUP_POW_SUB_ALT = `!G (x:A) m n.
        x IN group_carrier G /\ n <= m
        ==> group_pow G x (m - n) =
            group_mul G (group_inv G (group_pow G x n)) (group_pow G x m)`;;

let GROUP_INV_POW = `!G (x:A) n.
        x IN group_carrier G
        ==> group_inv G (group_pow G x n) = group_pow G (group_inv G x) n`;;

let GROUP_POW_MUL = `!G (x:A) m n.
        x IN group_carrier G
        ==> group_pow G x (m * n) = group_pow G (group_pow G x m) n`;;

let GROUP_POW_POW = `!G (x:A) m n.
        x IN group_carrier G
        ==> group_pow G (group_pow G x m) n = group_pow G x (m * n)`;;

let GROUP_COMMUTES_POW = `!G (x:A) (y:A) n.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> group_mul G (group_pow G x n) y = group_mul G y (group_pow G x n)`;;

let GROUP_MUL_POW = `!G (x:A) (y:A) n.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> group_pow G (group_mul G x y) n =
            group_mul G (group_pow G x n) (group_pow G y n)`;;

let group_zpow = new_definition
 `group_zpow G (x:A) n =
    if &0 <= n then group_pow G x (num_of_int n)
    else group_inv G (group_pow G x (num_of_int(--n)))`;;

let GROUP_ZPOW = `!G (x:A) n. x IN group_carrier G ==> group_zpow G x n IN group_carrier G`;;

let GROUP_NPOW = `!G (x:A) n. group_zpow G x (&n) = group_pow G x n`;;

let GROUP_ZPOW_0 = `!G (x:A). group_zpow G x (&0) = group_id G`;;

let GROUP_ZPOW_1 = `!G x:A. x IN group_carrier G ==> group_zpow G x (&1) = x`;;

let GROUP_ZPOW_2 = `!G x:A. x IN group_carrier G ==> group_zpow G x (&2) = group_mul G x x`;;

let GROUP_ZPOW_ID = `!n. group_zpow G (group_id G) n = group_id G`;;

let GROUP_ZPOW_NEG = `!G (x:A) n.
        x IN group_carrier G
        ==> group_zpow G x (--n) = group_inv G (group_zpow G x n)`;;

let GROUP_ZPOW_MINUS1 = `!G x:A. x IN group_carrier G ==> group_zpow G x (-- &1) = group_inv G x`;;

let GROUP_ZPOW_POW = `(!G (x:A) n. group_zpow G x (&n) = group_pow G x n) /\
   (!G (x:A) n. group_zpow G x (-- &n) = group_inv G (group_pow G x n))`;;

let GROUP_ZPOW_ABS_EQ_ID = `!G (x:A) n.
        x IN group_carrier G
        ==> (group_zpow G x (abs n) = group_id G <=>
             group_zpow G x n = group_id G)`;;

let GROUP_ZPOW_ADD = `!G (x:A) m n.
        x IN group_carrier G
        ==> group_zpow G x (m + n) =
            group_mul G (group_zpow G x m) (group_zpow G x n)`;;

let GROUP_ZPOW_SUB = `!G (x:A) m n.
        x IN group_carrier G
        ==> group_zpow G x (m - n) =
            group_div G (group_zpow G x m) (group_zpow G x n)`;;

let GROUP_ZPOW_SUB_ALT = `!G (x:A) m n.
        x IN group_carrier G
        ==> group_zpow G x (m - n) =
            group_mul G (group_inv G (group_zpow G x n)) (group_zpow G x m)`;;

let GROUP_INV_ZPOW = `!G (x:A) n.
        x IN group_carrier G
        ==> group_inv G (group_zpow G x n) = group_zpow G (group_inv G x) n`;;

let GROUP_ZPOW_INV = `!G (x:A) n.
        x IN group_carrier G
        ==> group_zpow G (group_inv G x) n = group_zpow G x (--n)`;;

let GROUP_ZPOW_MUL = `!G (x:A) m n.
        x IN group_carrier G
        ==> group_zpow G x (m * n) = group_zpow G (group_zpow G x m) n`;;

let GROUP_COMMUTES_ZPOW = `!G (x:A) (y:A) n.
      x IN group_carrier G /\ y IN group_carrier G /\
      group_mul G x y = group_mul G y x
      ==> group_mul G (group_zpow G x n) y = group_mul G y (group_zpow G x n)`;;

let GROUP_MUL_ZPOW = `!G (x:A) (y:A) n.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> group_zpow G (group_mul G x y) n =
            group_mul G (group_zpow G x n) (group_zpow G y n)`;;

(* ------------------------------------------------------------------------- *)
(* Abelian groups.                                                           *)
(* ------------------------------------------------------------------------- *)

let abelian_group = new_definition
 `abelian_group (G:A group) <=>
  !x y. x IN group_carrier G /\ y IN group_carrier G
        ==> group_mul G x y = group_mul G y x`;;

let TRIVIAL_IMP_ABELIAN_GROUP = `!G:A group. trivial_group G ==> abelian_group G`;;

let ABELIAN_SINGLETON_GROUP = `!a:A. abelian_group(singleton_group a)`;;

let ABELIAN_OPPOSITE_GROUP = `!G:A group. abelian_group (opposite_group G) <=> abelian_group G`;;

let ABELIAN_GROUP_MUL_POW = `!G (x:A) (y:A) n.
        abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> group_pow G (group_mul G x y) n =
            group_mul G (group_pow G x n) (group_pow G y n)`;;

let ABELIAN_GROUP_MUL_ZPOW = `!G (x:A) (y:A) n.
        abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> group_zpow G (group_mul G x y) n =
            group_mul G (group_zpow G x n) (group_zpow G y n)`;;

let ABELIAN_GROUP_DIV_ZPOW = `!G x (y:A) n.
        abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> group_zpow G (group_div G x y) n =
            group_div G (group_zpow G x n) (group_zpow G y n)`;;

let ABELIAN_GROUP_MUL_AC = `!G:A group.
        abelian_group G <=>
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> group_mul G x y = group_mul G y x) /\
        (!x y z. x IN group_carrier G /\ y IN group_carrier G /\
                 z IN group_carrier G
                 ==> group_mul G (group_mul G x y) z =
                     group_mul G x (group_mul G y z)) /\
        (!x y z. x IN group_carrier G /\ y IN group_carrier G /\
                 z IN group_carrier G
                 ==> group_mul G x (group_mul G y z) =
                     group_mul G y (group_mul G x z))`;;

(* ------------------------------------------------------------------------- *)
(* Totalized versions of the group operations (using additive terminology    *)
(* for variety's sake). This totalization can be quite convenient, e.g. for  *)
(* normalization and use of the "iterate" construct in the Abelian case.     *)
(* ------------------------------------------------------------------------- *)

let group_neg = new_definition
 `group_neg G x = if x IN group_carrier G then group_inv G x else x`;;

let group_add = new_definition
 `group_add G x (y:A) =
        if x IN group_carrier G /\ y IN group_carrier G
        then group_mul G x y
        else if x IN group_carrier G then y
        else if y IN group_carrier G then x
        else @w. ~(w IN group_carrier G)`;;

let group_nmul = new_recursive_definition num_RECURSION
 `group_nmul G 0 x = group_id G /\
  group_nmul G (SUC n) x = group_add G x (group_nmul G n x)`;;

let GROUP_NEG = `!G x:A. group_neg G x IN group_carrier G <=> x IN group_carrier G`;;

let GROUP_ADD = `!G x y:A.
        group_add G x y IN group_carrier G <=>
        x IN group_carrier G /\ y IN group_carrier G`;;

let GROUP_NEG_EQ_INV = `!G x:A. x IN group_carrier G ==> group_neg G x = group_inv G x`;;

let GROUP_ADD_EQ_MUL = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> group_add G x y = group_mul G x y`;;

let GROUP_ADD_LID = `!G x:A. group_add G (group_id G) x = x`;;

let GROUP_ADD_RID = `!G x:A. group_add G x (group_id G) = x`;;

let GROUP_ADD_ASSOC = `!G x y z:A.
        group_add G x (group_add G y z) = group_add G (group_add G x y) z`;;

let GROUP_NEG_ADD = `!G x y:A. group_neg G (group_add G x y) =
             group_add G (group_neg G y) (group_neg G x)`;;

let GROUP_NEG_NEG = `!G x:A. group_neg G (group_neg G x) = x`;;

let GROUP_NEG_ID = `!G:A group. group_neg G (group_id G) = group_id G`;;

let GROUP_ADD_EQ_ID = `!G x y:A. group_add G x y = group_id G <=> group_add G y x = group_id G`;;

let GROUP_NEG_EQ_ID = `!G x:A. group_neg G x = group_id G <=> x = group_id G`;;

let GROUP_NMUL_EQ_POW = `!G (x:A) n. x IN group_carrier G ==> group_nmul G n x = group_pow G x n`;;

let GROUP_NMUL_ADD = `!G (x:A) m n.
        group_nmul G (m + n) x =
        group_add G (group_nmul G m x) (group_nmul G n x)`;;

let GROUP_NMUL_MUL = `!G (x:A) m n.
        group_nmul G (m * n) x = group_nmul G m (group_nmul G n x)`;;

let GROUP_NMUL_1 = `!G x:A. group_nmul G 1 x = x`;;

let GROUP_NEG_NMUL = `!G (x:A) n.
        group_neg G (group_nmul G n x) = group_nmul G n (group_neg G x)`;;

let GROUP_ADD_SYM = `!G x y:A. abelian_group G ==> group_add G x y = group_add G y x`;;

let GROUP_ADD_SYM_EQ = `!G:A group. (!x y. group_add G x y = group_add G y x) <=> abelian_group G`;;

let GROUP_ADD_NMUL = `!G (x:A) y n.
        abelian_group G
        ==> group_nmul G n (group_add G x y) =
            group_add G (group_nmul G n x) (group_nmul G n y)`;;

let NEUTRAL_GROUP_ADD = `!G:A group. neutral(group_add G) = group_id G`;;

let MONOIDAL_GROUP_ADD = `!G:A group. monoidal(group_add G) <=> abelian_group G`;;

(* ------------------------------------------------------------------------- *)
(* Procedure for equations s = t or equivalences s = t <=> s' = t' in        *)
(* the theory of groups, which will generate carrier membership              *)
(* conditions if they are not explicitly presented as an implication,        *)
(* e.g.                                                                      *)
(*                                                                           *)
(* GROUP_RULE                                                                *)
(*  `group_mul G a (group_inv G (group_mul G b a)) =                         *)
(*   group_inv G (group_mul G (group_inv G c) (group_mul G c b))`;;          *)
(*                                                                           *)
(* GROUP_RULE                                                                *)
(*  `!G x y z:A.                                                             *)
(*         x IN group_carrier G /\                                           *)
(*         y IN group_carrier G /\                                           *)
(*         z IN group_carrier G                                              *)
(*         ==> (group_mul G (group_div G z y)                                *)
(*                          (group_mul G x (group_div G y z)) =              *)
(*              group_id G <=>                                               *)
(*              group_inv G (group_mul G x y) = group_inv G y)`;;            *)
(* ------------------------------------------------------------------------- *)

let GROUP_RULE =
  let rec GROUP_MEM tm =
    if is_conj tm then CONJ (GROUP_MEM(lhand tm)) (GROUP_MEM(rand tm)) else
    try PART_MATCH I GROUP_ID tm with Failure _ ->
    try let th = try PART_MATCH rand GROUP_INV tm with Failure _ ->
                 try PART_MATCH rand GROUP_POW tm with Failure _ ->
                 try PART_MATCH rand GROUP_ZPOW tm with Failure _ ->
                 try PART_MATCH rand GROUP_MUL tm with Failure _ ->
                 PART_MATCH rand GROUP_DIV tm in
        MP th (GROUP_MEM(lhand(concl th)))
    with Failure _ -> ASSUME tm in
  let GROUP_REWR_CONV th =
    if not(is_imp(snd(strip_forall(concl th)))) then REWR_CONV th else
    let mfn = PART_MATCH (lhand o rand) th in
    fun tm -> let ith = mfn tm in MP ith (GROUP_MEM(lhand(concl ith))) in
  let GROUP_CANONIZE_CONV =
    let mfn_inv = (MATCH_MP o prove)
     (`!G t t':A.
            t = t' /\ t IN group_carrier G
            ==> group_inv G t = group_neg G t' /\
                group_inv G t IN group_carrier G`,
      SIMP_TAC[IMP_CONJ; group_neg; GROUP_INV])
    and mfn_neg = (MATCH_MP o prove)
     (`!G t t':A.
            t = t' /\ t IN group_carrier G
            ==> group_neg G t = group_neg G t' /\
                group_neg G t IN group_carrier G`,
      SIMP_TAC[GROUP_NEG])
    and mfn_pow = (MATCH_MP o prove)
     (`!G t (t':A) n.
            t = t' /\ t IN group_carrier G
            ==> group_pow G t n = group_nmul G n t' /\
                group_pow G t n IN group_carrier G`,
      SIMP_TAC[GROUP_NMUL_EQ_POW; IMP_CONJ; GROUP_POW])
    and mfn_nmul = (MATCH_MP o prove)
     (`!G t (t':A) n.
            t = t' /\ t IN group_carrier G
            ==> group_nmul G n t = group_nmul G n t' /\
                group_nmul G n t IN group_carrier G`,
      SIMP_TAC[GROUP_NMUL_EQ_POW; GROUP_POW; IMP_CONJ])
    and mfn_mul = (MATCH_MP o prove)
     (`!G s t s' t':A.
            (s = s' /\ s IN group_carrier G) /\
            (t = t' /\ t IN group_carrier G)
            ==> group_mul G s t = group_add G s' t' /\
                group_mul G s t IN group_carrier G`,
      SIMP_TAC[IMP_CONJ; group_add; GROUP_MUL])
    and mfn_add = (MATCH_MP o prove)
     (`!G s t s' t':A.
            (s = s' /\ s IN group_carrier G) /\
            (t = t' /\ t IN group_carrier G)
            ==> group_add G s t = group_add G s' t' /\
                group_add G s t IN group_carrier G`,
      SIMP_TAC[GROUP_ADD])
    and in_tm = `(IN):A->(A->bool)->bool`
    and gc_tm = `group_carrier:(A)group->A->bool` in
    let rec GROUP_TOTALIZE g tm =
      match tm with
        Comb(Comb(Comb(Const("group_mul",_),g),s),t) ->
            mfn_mul(CONJ (GROUP_TOTALIZE g s) (GROUP_TOTALIZE g t))
      | Comb(Comb(Comb(Const("group_add",_),g),s),t) ->
            mfn_add(CONJ (GROUP_TOTALIZE g s) (GROUP_TOTALIZE g t))
      | Comb(Comb(Comb(Const("group_pow",_),g),t),n) ->
            SPEC n (mfn_pow(GROUP_TOTALIZE g t))
      | Comb(Comb(Comb(Const("group_nmul",_),g),n),t) ->
            SPEC n (mfn_nmul(GROUP_TOTALIZE g t))
      | Comb(Comb(Const("group_inv",_),g),t) ->
            mfn_inv(GROUP_TOTALIZE g t)
      | Comb(Comb(Const("group_neg",_),g),t) ->
            mfn_neg(GROUP_TOTALIZE g t)
      | Comb(Const("group_id",_),g) ->
          CONJ (REFL tm) (ISPEC g GROUP_ID)
      | _ ->
          let ifn = inst[type_of tm,aty] in
          CONJ (REFL tm)
               (ASSUME(mk_comb(mk_comb(ifn in_tm,tm),mk_comb(ifn gc_tm,g)))) in
    let GROUP_CANONIZE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("group_mul",_),g),s),t)
      | Comb(Comb(Comb(Const("group_add",_),g),s),t)
      | Comb(Comb(Comb(Const("group_pow",_),g),s),t)
      | Comb(Comb(Comb(Const("group_nmul",_),g),s),t) ->
          CONJUNCT1(GROUP_TOTALIZE g tm)
      | Comb(Comb(Const("group_inv",_),g),t)
      | Comb(Comb(Const("group_neg",_),g),t) ->
          CONJUNCT1(GROUP_TOTALIZE g tm)
      | _ -> REFL tm in
    NUM_REDUCE_CONV THENC INT_REDUCE_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GROUP_ZPOW_POW; group_div] THENC
    GROUP_CANONIZE_CONV in
  let GROUP_NORM_CONV =
    let conv = (FIRST_CONV o map GROUP_REWR_CONV o CONJUNCTS o prove)
     (`(!G x:A. x IN group_carrier G
                ==> group_add G x (group_neg G x) = group_id G) /\
       (!G x:A. x IN group_carrier G
                ==> group_add G (group_neg G x) x = group_id G) /\
       (!G x y:A. x IN group_carrier G
                ==> group_add G x (group_add G (group_neg G x) y) = y) /\
       (!G x y:A. x IN group_carrier G
                ==> group_add G (group_neg G x) (group_add G x y) = y)`,
      REWRITE_TAC[GROUP_ADD_ASSOC] THEN
      SIMP_TAC[GROUP_NEG_EQ_INV; GROUP_ADD_EQ_MUL; GROUP_MUL_LINV;
               GROUP_MUL_RINV; GROUP_INV; GROUP_ADD_LID]) in
    let rec GROUP_NMUL_CONV tm =
      try REWR_CONV (CONJUNCT1 group_nmul) tm with Failure _ ->
      (LAND_CONV num_CONV THENC
       REWR_CONV(CONJUNCT2 group_nmul) THENC
       RAND_CONV GROUP_NMUL_CONV) tm in
    GROUP_CANONIZE_CONV THENC
    TOP_DEPTH_CONV GROUP_NMUL_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [GROUP_NEG_ADD; GROUP_NEG_NEG; GROUP_NEG_ID] THENC
    GEN_REWRITE_CONV DEPTH_CONV [GROUP_ADD_LID; GROUP_ADD_RID] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM GROUP_ADD_ASSOC] THENC
    TOP_DEPTH_CONV
     (GEN_REWRITE_CONV I [GROUP_ADD_LID; GROUP_ADD_RID] ORELSEC conv) in
  let GROUP_EQ_RULE tm =
    let l,r = dest_eq tm in
    TRANS (GROUP_NORM_CONV l) (SYM(GROUP_NORM_CONV r)) in
  let is_groupty ty = match ty with Tyapp("group",[a]) -> true | _ -> false in
  let rec list_of_gtm tm =
    match tm with
      Comb(Const("group_id",_),_) -> []
    | Comb(Comb(Const("group_neg",_),_),x) -> [false,x]
    | Comb(Comb(Comb(Const("group_add",_),_),
       Comb(Comb(Const("group_neg",_),_),x)),y) -> (false,x)::list_of_gtm y
    | Comb(Comb(Comb(Const("group_add",_),_),x),y) -> (true,x)::list_of_gtm y
    | _ -> [true,tm] in
  let find_rot l l' =
    find (fun n -> let l1,l2 = chop_list n l in l2@l1 = l')
         (0--(length l - 1)) in
  let rec GROUP_REASSOC_CONV n tm =
    if n = 0 then REFL tm
    else (REWR_CONV GROUP_ADD_ASSOC THENC GROUP_REASSOC_CONV(n-1)) tm in
  let GROUP_ROTATE_CONV n =
    if n = 0 then REFL else
    LAND_CONV(GROUP_REASSOC_CONV(n - 1)) THENC
    REWR_CONV GROUP_ADD_EQ_ID THENC
    LAND_CONV GROUP_NORM_CONV in
  let rec GROUP_EQ_HYPERNORM_CONV tm =
    let ts = list_of_gtm(lhand tm) in
    if length ts > 2 &&
       (let p,v = hd ts and q,w = last ts in not(p = q) && v = w)
    then (GROUP_ROTATE_CONV 1 THENC GROUP_EQ_HYPERNORM_CONV) tm
    else REFL tm in
  fun tm ->
    let gvs = setify(find_terms (is_groupty o type_of) tm) in
    if gvs = [] then MESON[] tm else
    if length gvs > 1 then failwith "GROUP_RULE: Several groups involved" else
    let g = hd gvs in
    let GROUP_EQ_NORM_CONV =
      GROUP_REWR_CONV(GSYM(ISPEC g GROUP_DIV_EQ_ID)) THENC
      LAND_CONV GROUP_NORM_CONV in
    let avs,bod = strip_forall tm in
    let ant,con = if is_imp bod then [lhand bod],rand bod else [],bod in
    let th1 =
      if not(is_iff con) then GROUP_EQ_RULE con else
      let eq1,eq2 = dest_iff con in
      let th1 = (GROUP_EQ_NORM_CONV THENC GROUP_EQ_HYPERNORM_CONV) eq1
      and th2 = (GROUP_EQ_NORM_CONV THENC GROUP_EQ_HYPERNORM_CONV) eq2 in
      let ls1 = list_of_gtm(lhand(rand(concl th1)))
      and ls2 = list_of_gtm(lhand(rand(concl th2))) in
      try let n = find_rot ls1 ls2 in
          TRANS (CONV_RULE(RAND_CONV(GROUP_ROTATE_CONV n)) th1) (SYM th2)
      with Failure _ ->
          let th1' =
            GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV)
              [GSYM GROUP_ADD_ASSOC]
              (GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV)
               [GROUP_NEG_ADD; GROUP_NEG_NEG]
               (GEN_REWRITE_RULE RAND_CONV [GSYM GROUP_NEG_EQ_ID] th1))
          and ls1' = map (fun (p,v) -> not p,v) (rev ls1) in
          let n = find_rot ls1' ls2 in
          TRANS (CONV_RULE(RAND_CONV(GROUP_ROTATE_CONV n)) th1') (SYM th2) in
    let th2 =
      if ant = [] then th1
      else itlist PROVE_HYP (CONJUNCTS(ASSUME(hd ant))) th1 in
    let asl = hyp th2 in
    let th3 =
      if asl = [] then th2 else
      let asm = list_mk_conj asl in
      DISCH asm (itlist PROVE_HYP (CONJUNCTS(ASSUME asm)) th2) in
    let th4 = GENL avs th3 in
    let bvs = frees(concl th4) in
    GENL (sort (<) bvs) th4;;

let GROUP_TAC =
  REPEAT GEN_TAC THEN
  TRY(MATCH_MP_TAC(MESON[] `(u = v <=> s = t) ==> (u = v ==> s = t)`)) THEN
  W(fun (asl,w) ->
        let th = GROUP_RULE w in
        (MATCH_ACCEPT_TAC th ORELSE
         (MATCH_MP_TAC th THEN ASM_REWRITE_TAC[])));;

(* ------------------------------------------------------------------------- *)
(* Iterated operation on groups, the first one being in a specific           *)
(* order given as an argument, the latter picking some arbitrary             *)
(* wellorder, usually with the expectation that it will be immaterial.       *)
(* ------------------------------------------------------------------------- *)

let group_product = new_definition
 `group_product (G:A group) =
        iterato (group_carrier G) (group_id G) (group_mul G)`;;

let group_sum = new_definition
 `group_sum (G:A group) =
        group_product G (@l. woset l /\ fld l = (:K))`;;

let GROUP_PRODUCT_EQ = `!G (<<=) k (f:K->A) g.
        (!i. i IN k ==> f i = g i)
        ==> group_product G (<<=) k f = group_product G (<<=) k g`;;

let GROUP_SUM_EQ = `!G k (f:K->A) g.
        (!i. i IN k ==> f i = g i) ==> group_sum G k f = group_sum G k g`;;

let th = `(!G (<<=) k f (g:K->A).
         (!i. i IN k ==> f i = g i)
         ==> group_product G (<<=) k (\i. f i) = group_product G (<<=) k g) /\
   (!G k f (g:K->A).
         (!i. i IN k ==> f i = g i)
         ==> group_sum G k (\i. f i) = group_sum G k g)`;;

let GROUP_PRODUCT_CLOSED = `!P G (<<=) k (f:K->A).
       P(group_id G) /\
       (!x y. x IN group_carrier G /\ y IN group_carrier G /\
              P x /\ P y
              ==> P(group_mul G x y)) /\
       (!i. i IN k /\ f i IN group_carrier G /\ ~(f i = group_id G) ==> P(f i))
       ==> P(group_product G (<<=) k f)`;;

let GROUP_SUM_CLOSED = `!P G k (f:K->A).
       P(group_id G) /\
       (!x y. x IN group_carrier G /\ y IN group_carrier G /\
              P x /\ P y
              ==> P(group_mul G x y)) /\
       (!i. i IN k /\ f i IN group_carrier G /\ ~(f i = group_id G) ==> P(f i))
       ==> P(group_sum G k f)`;;

let GROUP_PRODUCT = `!G (<<=) k (f:K->A). group_product G (<<=) k f IN group_carrier G`;;

let GROUP_SUM = `!G k (f:K->A). group_sum G k f IN group_carrier G`;;

let GROUP_PRODUCT_SUPPORT = `!G (<<=) k (f:K->A).
        group_product G (<<=) {i | i IN k /\ ~(f i = group_id G)} f =
        group_product G (<<=) k f`;;

let GROUP_SUM_SUPPORT = `!G k (f:K->A).
      group_sum G {i | i IN k /\ ~(f i = group_id G)} f =
      group_sum G k f`;;

let GROUP_PRODUCT_RESTRICT = `!G (<<=) k (f:K->A).
        group_product G (<<=) {i | i IN k /\ f i IN group_carrier G} f =
        group_product G (<<=) k f`;;

let GROUP_SUM_RESTRICT = `!G k (f:K->A).
        group_sum G {i | i IN k /\ f i IN group_carrier G} f =
        group_sum G k f`;;

let GROUP_PRODUCT_EXPAND_CASES = `!G (<<=) k (f:K->A).
        group_product G (<<=) k f =
        if FINITE {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}}
        then group_product G (<<=)
              {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} f
        else group_id G`;;

let GROUP_SUM_EXPAND_CASES = `!G k (f:K->A).
        group_sum G k f =
        if FINITE {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}}
        then group_sum G
              {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} f
        else group_id G`;;

let GROUP_PRODUCT_RESTRICT_SET = `!G (<<=) P s (f:K->A).
        group_product G (<<=) {x | x IN s /\ P x} f =
        group_product G (<<=) s (\x. if P x then f x else group_id G)`;;

let GROUP_SUM_RESTRICT_SET = `!G P s (f:K->A).
        group_sum G {x | x IN s /\ P x} f =
        group_sum G s (\x. if P x then f x else group_id G)`;;

let GROUP_PRODUCT_SUPERSET = `!G (<<=) s t (f:K->A).
        t SUBSET s /\ (!x. x IN s /\ ~(x IN t) ==> f x = group_id G)
        ==> group_product G (<<=) s f = group_product G (<<=) t f`;;

let GROUP_SUM_SUPERSET = `!G s t (f:K->A).
        t SUBSET s /\ (!x. x IN s /\ ~(x IN t) ==> f x = group_id G)
        ==> group_sum G s f = group_sum G t f`;;

let GROUP_PRODUCT_CLAUSES = `!G (<<=) (f:K->A).
      group_product G (<<=) {} f = group_id G /\
      (!i k. FINITE {j | j IN k /\ f j IN group_carrier G DIFF {group_id G}} /\
             (!j. j IN k ==> i <<= j /\ ~(j <<= i))
             ==> group_product G (<<=) (i INSERT k) f =
                   if f i IN group_carrier G ==> i IN k
                   then group_product G (<<=) k f
                   else group_mul G (f i) (group_product G (<<=) k f))`;;

let GROUP_PRODUCT_CLAUSES_EXISTS = `!G (<<=) (f:K->A).
      group_product G (<<=) {} f = group_id G /\
      (!k. FINITE {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} /\
           ~({i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} = {})
           ==> ?i. i IN k /\
                   f i IN group_carrier G DIFF {group_id G} /\
                   group_product G (<<=) k f =
                   group_mul G (f i) (group_product G (<<=) (k DELETE i) f))`;;

let GROUP_SUM_CLAUSES_EXISTS = `!G (f:K->A).
      group_sum G {} f = group_id G /\
      (!k. FINITE {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} /\
           ~({i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} = {})
           ==> ?i. i IN k /\
                   f i IN group_carrier G DIFF {group_id G} /\
                   group_sum G k f =
                   group_mul G (f i) (group_sum G (k DELETE i) f))`;;

let GROUP_PRODUCT_EQ_ID = `!(G:A group) (<<=) (s:K->bool) f.
        (!i. i IN s ==> f i = group_id G)
        ==> group_product G (<<=) s f = group_id G`;;

let GROUP_SUM_EQ_ID = `!(G:A group) (s:K->bool) f.
        (!i. i IN s ==> f i = group_id G)
        ==> group_sum G s f = group_id G`;;

let GROUP_PRODUCT_ID = `!(G:A group) (<<=) (s:K->bool).
        group_product G (<<=) s (\x. group_id G) = group_id G`;;

let GROUP_SUM_ID = `!(G:A group) (s:K->bool).
        group_sum G s (\x. group_id G) = group_id G`;;

let GROUP_COMMUTES_PRODUCT = `!G (<<=) k (f:K->A) z.
        (!i. i IN k /\ f i IN group_carrier G /\ ~(f i = group_id G)
             ==> group_mul G (f i) z = group_mul G z (f i)) /\
        z IN group_carrier G
        ==> group_mul G (group_product G (<<=) k f) z =
            group_mul G z (group_product G (<<=) k f)`;;

let GROUP_COMMUTES_SUM = `!G k (f:K->A) z.
        (!i. i IN k /\ f i IN group_carrier G /\ ~(f i = group_id G)
             ==> group_mul G (f i) z = group_mul G z (f i)) /\
        z IN group_carrier G
        ==> group_mul G (group_sum G k f) z = group_mul G z (group_sum G k f)`;;

let GROUP_PRODUCT_SING = `!G (<<=) i (f:K->A).
        group_product G (<<=) {i} f =
        if f i IN group_carrier G then f i else group_id G`;;

let GROUP_SUM_SING = `!G i (f:K->A).
        group_sum G {i} f =
        if f i IN group_carrier G then f i else group_id G`;;

let GROUP_PRODUCT_UNION = `!G (<<=) (f:K->A) s t.
        woset(<<=) /\ fld(<<=) = (:K) /\
        (FINITE {i | i IN s /\ f i IN group_carrier G DIFF {group_id G}} <=>
         FINITE {i | i IN t /\ f i IN group_carrier G DIFF {group_id G}}) /\
        (!x y. x IN s /\ y IN t ==> x <<= y /\ ~(x = y))
        ==> group_product G (<<=) (s UNION t) f =
            group_mul G (group_product G (<<=) s f)
                        (group_product G (<<=) t f)`;;

let GROUP_PRODUCT_CLAUSES_LEFT = `!G (f:num->A) m n.
        group_product G (<=) (m..n) f =
        if m <= n then
           if f m IN group_carrier G
           then group_mul G (f m) (group_product G (<=) (m+1..n) f)
           else group_product G (<=) (m+1..n) f
         else group_id G`;;

let GROUP_PRODUCT_CLAUSES_RIGHT = `!G (f:num->A) m n.
        group_product G (<=) (m..n) f =
        if m <= n then
           if f n IN group_carrier G
           then if n = 0 then f 0
                else group_mul G (group_product G (<=) (m..n-1) f) (f n)
           else group_product G (<=) (m..n-1) f
         else group_id G`;;

let GROUP_PRODUCT_CLAUSES_NUMSEG = `(!G m f:num->A.
        group_product G (<=) (m..0) f =
        if m = 0 /\ f 0 IN group_carrier G then f 0 else group_id G) /\
   (!G m n f:num->A.
        group_product G (<=) (m..SUC n) f =
        if m <= SUC n /\ f(SUC n) IN group_carrier G
        then group_mul G (group_product G (<=) (m..n) f) (f(SUC n))
        else group_product G (<=) (m..n) f)`;;

let GROUP_PRODUCT_CLAUSES_COMMUTING = `!G (<<=) i k (f:K->A).
        woset(<<=) /\ fld(<<=) = (:K) /\
        FINITE {j | j IN k /\ f j IN group_carrier G DIFF {group_id G}} /\
        (!j. j IN k /\ j <<= i /\ ~(j = i) /\
             f i IN group_carrier G /\ f j IN group_carrier G
             ==> group_mul G (f i) (f j) = group_mul G (f j) (f i))
        ==> group_product G (<<=) (i INSERT k) f =
                if f i IN group_carrier G ==> i IN k
                then group_product G (<<=) k f
                else group_mul G (f i) (group_product G (<<=) k f)`;;

let ABELIAN_GROUP_PRODUCT_CLAUSES = `!G (<<=) i k (f:K->A).
        woset(<<=) /\ fld(<<=) = (:K) /\
        abelian_group G /\
        FINITE {j | j IN k /\ f j IN group_carrier G DIFF {group_id G}}
        ==> group_product G (<<=) (i INSERT k) f =
                if f i IN group_carrier G ==> i IN k
                then group_product G (<<=) k f
                else group_mul G (f i) (group_product G (<<=) k f)`;;

let GROUP_SUM_CLAUSES_COMMUTING = `!G i k (f:K->A).
        FINITE {j | j IN k /\ f j IN group_carrier G DIFF {group_id G}} /\
        (!j. j IN k /\ ~(j = i) /\
             f i IN group_carrier G /\ f j IN group_carrier G
             ==> group_mul G (f i) (f j) = group_mul G (f j) (f i))
        ==> group_sum G (i INSERT k) f =
                if f i IN group_carrier G ==> i IN k
                then group_sum G k f
                else group_mul G (f i) (group_sum G k f)`;;

let ABELIAN_GROUP_SUM_CLAUSES = `!G i k (f:K->A).
        abelian_group G /\
        FINITE {j | j IN k /\ f j IN group_carrier G DIFF {group_id G}}
        ==> group_sum G (i INSERT k) f =
                if f i IN group_carrier G ==> i IN k
                then group_sum G k f
                else group_mul G (f i) (group_sum G k f)`;;

let GROUP_PRODUCT_MUL = `!G (<<=) k f (g:K->A).
      woset(<<=) /\ fld(<<=) = (:K) /\
      FINITE {i | i IN k /\ ~(f i = group_id G)} /\
      FINITE {i | i IN k /\ ~(g i = group_id G)} /\
      (!i. i IN k ==> f i IN group_carrier G /\ g i IN group_carrier G) /\
      pairwise (\i j. group_mul G (f i) (g j) = group_mul G (g j) (f i)) k
      ==> group_product G (<<=) k (\i. group_mul G (f i) (g i)) =
          group_mul G (group_product G (<<=) k f) (group_product G (<<=) k g)`;;

let GROUP_SUM_MUL = `!G k f (g:K->A).
        FINITE {i | i IN k /\ ~(f i = group_id G)} /\
        FINITE {i | i IN k /\ ~(g i = group_id G)} /\
        (!i. i IN k ==> f i IN group_carrier G /\ g i IN group_carrier G) /\
        pairwise (\i j. group_mul G (f i) (g j) = group_mul G (g j) (f i)) k
        ==> group_sum G k (\i. group_mul G (f i) (g i)) =
            group_mul G (group_sum G k f) (group_sum G k g)`;;

let ABELIAN_GROUP_SUM_MUL = `!G k f (g:K->A).
        abelian_group G /\
        FINITE {i | i IN k /\ ~(f i = group_id G)} /\
        FINITE {i | i IN k /\ ~(g i = group_id G)} /\
        (!i. i IN k ==> f i IN group_carrier G /\ g i IN group_carrier G)
        ==> group_sum G k (\i. group_mul G (f i) (g i)) =
            group_mul G (group_sum G k f) (group_sum G k g)`;;

let GROUP_SUM_INV = `!G k (f:K->A).
        FINITE {i | i IN k /\ ~(f i = group_id G)} /\
        (!i. i IN k ==> f i IN group_carrier G) /\
        pairwise (\i j. group_mul G (f i) (f j) = group_mul G (f j) (f i)) k
        ==> group_sum G k (\i. group_inv G (f i)) =
            group_inv G (group_sum G k f)`;;

let ABELIAN_GROUP_SUM_INV = `!G k (f:K->A).
        abelian_group G /\
        FINITE {i | i IN k /\ ~(f i = group_id G)} /\
        (!i. i IN k ==> f i IN group_carrier G)
        ==> group_sum G k (\i. group_inv G (f i)) =
            group_inv G (group_sum G k f)`;;

let GROUP_SUM_POW = `!G k (f:K->A) n.
        FINITE {i | i IN k /\ ~(f i = group_id G)} /\
        (!i. i IN k ==> f i IN group_carrier G) /\
        pairwise (\i j. group_mul G (f i) (f j) = group_mul G (f j) (f i)) k
        ==> group_sum G k (\i. group_pow G (f i) n) =
            group_pow G (group_sum G k f) n`;;

let ABELIAN_GROUP_SUM_POW = `!G k (f:K->A) n.
        abelian_group G /\
        FINITE {i | i IN k /\ ~(f i = group_id G)} /\
        (!i. i IN k ==> f i IN group_carrier G)
        ==> group_sum G k (\i. group_pow G (f i) n) =
            group_pow G (group_sum G k f) n`;;

let GROUP_SUM_ZPOW = `!G k (f:K->A) n.
        FINITE {i | i IN k /\ ~(f i = group_id G)} /\
        (!i. i IN k ==> f i IN group_carrier G) /\
        pairwise (\i j. group_mul G (f i) (f j) = group_mul G (f j) (f i)) k
        ==> group_sum G k (\i. group_zpow G (f i) n) =
            group_zpow G (group_sum G k f) n`;;

let ABELIAN_GROUP_SUM_ZPOW = `!G k (f:K->A) n.
        abelian_group G /\
        FINITE {i | i IN k /\ ~(f i = group_id G)} /\
        (!i. i IN k ==> f i IN group_carrier G)
        ==> group_sum G k (\i. group_zpow G (f i) n) =
            group_zpow G (group_sum G k f) n`;;

let GROUP_SUM_IMAGE = `!G (f:K->A) (g:A->B) s.
        abelian_group G /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> group_sum G (IMAGE f s) g = group_sum G s (g o f)`;;

let ABELIAN_GROUP_PRODUCT_ITERATE = `!G (<<=) (x:K->A) k.
        woset(<<=) /\
        fld(<<=) = (:K) /\
        abelian_group G /\
        (!i. i IN k ==> x i IN group_carrier G)
        ==> group_product G (<<=) k x = iterate (group_add G) k x`;;

let ABELIAN_GROUP_SUM_ITERATE = `!G (x:K->A) k.
        abelian_group G /\
        (!i. i IN k ==> x i IN group_carrier G)
        ==> group_sum G k x = iterate (group_add G) k x`;;

let ABELIAN_GROUP_ITERATE = `!G (x:K->A) k.
        abelian_group G /\
        (!i. i IN k ==> x i IN group_carrier G)
        ==> iterate (group_add G) k x IN group_carrier G`;;

(* ------------------------------------------------------------------------- *)
(* Congugation.                                                              *)
(* ------------------------------------------------------------------------- *)

let group_conjugation = new_definition
 `group_conjugation G a x = group_mul G a (group_mul G x (group_inv G a))`;;

let GROUP_CONJUGATION = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> group_conjugation G x y IN group_carrier G`;;

let GROUP_CONJUGATION_CONJUGATION = `!G a b x:A.
        a IN group_carrier G /\ b IN group_carrier G /\ x IN group_carrier G
        ==> group_conjugation G a (group_conjugation G b x) =
            group_conjugation G (group_mul G a b) x`;;

let GROUP_CONJUGATION_EQ = `!G a x y:A.
        a IN group_carrier G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (group_conjugation G a x = group_conjugation G a y <=> x = y)`;;

let GROUP_CONJUGATION_EQ_SELF = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_conjugation G x y = y <=>
             group_mul G x y = group_mul G y x)`;;

let GROUP_CONJUGATION_EQ_ID = `!G a x:A.
        a IN group_carrier G /\ x IN group_carrier G
        ==> (group_conjugation G a x = group_id G <=> x = group_id G)`;;

let GROUP_CONJUGATION_BY_ID = `!G x:A. x IN group_carrier G ==> group_conjugation G (group_id G) x = x`;;

let GROUP_CONJUGATION_LINV = `!G a x:A.
        a IN group_carrier G /\ x IN group_carrier G
        ==> group_conjugation G (group_inv G a) (group_conjugation G a x) = x`;;

let GROUP_CONJUGATION_RINV = `!G a x:A.
        a IN group_carrier G /\ x IN group_carrier G
        ==> group_conjugation G a (group_conjugation G (group_inv G a) x) = x`;;

let IN_IMAGE_GROUP_CONJUGATION = `!G s x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        s SUBSET group_carrier G
        ==> (x IN IMAGE (group_conjugation G y) s <=>
             group_conjugation G (group_inv G y) x IN s)`;;

let IMAGE_GROUP_CONJUGATION_SUBSET = `!G (a:A) s.
        a IN group_carrier G /\ s SUBSET group_carrier G
        ==> IMAGE (group_conjugation G a) s SUBSET group_carrier G`;;

let IMAGE_GROUP_CONJUGATION_BY_ID = `!G s:A->bool.
        s SUBSET group_carrier G
        ==> IMAGE (group_conjugation G (group_id G)) s = s`;;

let IMAGE_GROUP_CONJUGATION_BY_MUL = `!G s a b:A.
        a IN group_carrier G /\
        b IN group_carrier G /\
        s SUBSET group_carrier G
        ==> IMAGE (group_conjugation G (group_mul G a b)) s =
            IMAGE (group_conjugation G a) (IMAGE (group_conjugation G b) s)`;;

let IMAGE_GROUP_CONJUGATION_BY_INV = `!G (a:A) s t.
        a IN group_carrier G /\
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G
        ==> (IMAGE (group_conjugation G (group_inv G a)) s = t <=>
             IMAGE (group_conjugation G a) t = s)`;;

let IMAGE_GROUP_CONJUGATION_EQ_SWAP = `!G (a:A) s t.
        a IN group_carrier G /\
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G /\
        IMAGE (group_conjugation G (group_inv G a)) s = t
        ==> IMAGE (group_conjugation G a) t = s`;;

let IMAGE_GROUP_CONJUGATION_EQ_PREIMAGE = `!G (a:A) s t.
        a IN group_carrier G /\
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G
        ==> (IMAGE (group_conjugation G a) s = t <=>
             {x | x IN group_carrier G /\
                  group_conjugation G a x IN t} = s)`;;

(* ------------------------------------------------------------------------- *)
(* Subgroups. We treat them as *sets* which seems to be a common convention. *)
(* And "subgroup_generated" can be used in the degenerate case where the set *)
(* is closed under the operations to cast from "subset" to "group".          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("subgroup_of",(12,"right"));;

let subgroup_of = new_definition
  `(s:A->bool) subgroup_of (G:A group) <=>
        s SUBSET group_carrier G /\
        group_id G IN s /\
        (!x. x IN s ==> group_inv G x IN s) /\
        (!x y. x IN s /\ y IN s ==> group_mul G x y IN s)`;;

let IN_SUBGROUP_ID = `!G h:A->bool. h subgroup_of G ==> group_id G IN h`;;

let IN_SUBGROUP_INV = `!G h x:A. h subgroup_of G /\ x IN h ==> group_inv G x IN h`;;

let IN_SUBGROUP_MUL = `!G h x y:A. h subgroup_of G /\ x IN h /\ y IN h ==> group_mul G x y IN h`;;

let IN_SUBGROUP_DIV = `!G h x y:A. h subgroup_of G /\ x IN h /\ y IN h ==> group_div G x y IN h`;;

let IN_SUBGROUP_POW = `!G h (x:A) n. h subgroup_of G /\ x IN h ==> group_pow G x n IN h`;;

let IN_SUBGROUP_ZPOW = `!G h (x:A) n. h subgroup_of G /\ x IN h ==> group_zpow G x n IN h`;;

let IN_SUBGROUP_CONJUGATION = `!G h a x:A.
        h subgroup_of G /\ a IN h /\ x IN h ==> group_conjugation G a x IN h`;;

let IN_SUBGROUP_PRODUCT = `!G h (<<=) k (f:K->A).
        h subgroup_of G /\
        (!i. i IN k /\ f i IN group_carrier G ==> f i IN h)
        ==> group_product G (<<=) k f IN h`;;

let IN_SUBGROUP_SUM = `!G h k (f:K->A).
        h subgroup_of G /\
        (!i. i IN k /\ f i IN group_carrier G ==> f i IN h)
        ==> group_sum G k f IN h`;;

let IMAGE_GROUP_CONJUGATION_SUBGROUP = `!G h a:A.
        h subgroup_of G /\ a IN h ==> IMAGE (group_conjugation G a) h = h`;;

let SUBGROUP_OF_INTERS = `!G (gs:(A->bool)->bool).
        (!g. g IN gs ==> g subgroup_of G) /\ ~(gs = {})
        ==> (INTERS gs) subgroup_of G`;;

let SUBGROUP_OF_INTER = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G ==> (g INTER h) subgroup_of G`;;

let SUBGROUP_OF_UNIONS = `!G (u:(A->bool)->bool).
        ~(u = {}) /\
        (!h. h IN u ==> h subgroup_of G) /\
        (!g h. g IN u /\ h IN u ==> g SUBSET h \/ h SUBSET g)
        ==> (UNIONS u) subgroup_of G`;;

let SUBGROUP_OF_OPPOSITE_GROUP = `!G h:A->bool. h subgroup_of opposite_group G <=> h subgroup_of G`;;

let SUBGROUP_OF_IMP_SUBSET = `!G s:A->bool. s subgroup_of G ==> s SUBSET group_carrier G`;;

let SUBGROUP_OF_IMP_NONEMPTY = `!G s:A->bool. s subgroup_of G ==> ~(s = {})`;;

let TRIVIAL_SUBGROUP_OF = `!G:A group. {group_id G} subgroup_of G`;;

let CARRIER_SUBGROUP_OF = `!G:A group. (group_carrier G) subgroup_of G`;;

let FINITE_SUBGROUPS = `!(G:A group). FINITE(group_carrier G) ==> FINITE {h | h subgroup_of G}`;;

let FINITE_RESTRICTED_SUBGROUPS = `!P (G:A group).
        FINITE(group_carrier G) ==> FINITE {h | h subgroup_of G /\ P h}`;;

let subgroup_generated = new_definition
 `subgroup_generated G (s:A->bool) =
      group(INTERS {h | h subgroup_of G /\ (group_carrier G INTER s) SUBSET h},
            group_id G,group_inv G,group_mul G)`;;

let SUBGROUP_GENERATED = `(!G s:A->bool.
        group_carrier (subgroup_generated G s) =
          INTERS {h | h subgroup_of G /\ (group_carrier G INTER s) SUBSET h}) /\
    (!G s:A->bool. group_id (subgroup_generated G s) = group_id G) /\
    (!G s:A->bool. group_inv (subgroup_generated G s) = group_inv G) /\
    (!G s:A->bool. group_mul (subgroup_generated G s) = group_mul G)`;;

let SUBGROUP_GENERATED_EQ = `!G s:A->bool.
        subgroup_generated G s = G <=>
        group_carrier(subgroup_generated G s) = group_carrier G`;;

let GROUP_ID_SUBGROUP = `!G s:A->bool. group_id G IN group_carrier(subgroup_generated G s)`;;

let GROUP_INV_SUBGROUP = `!x. x IN group_carrier (subgroup_generated G s)
       ==> group_inv G x IN group_carrier(subgroup_generated G s)`;;

let GROUP_MUL_SUBGROUP = `!x y. x IN group_carrier (subgroup_generated G s) /\
         y IN group_carrier (subgroup_generated G s)
         ==> group_mul G x y IN group_carrier(subgroup_generated G s)`;;

let ABELIAN_SUBGROUP_GENERATED = `!G h:A->bool.
        abelian_group G ==> abelian_group(subgroup_generated G h)`;;

let GROUP_DIV_SUBGROUP_GENERATED = `!G s:A->bool. group_div (subgroup_generated G s) = group_div G`;;

let GROUP_POW_SUBGROUP_GENERATED = `!G s:A->bool. group_pow (subgroup_generated G s) = group_pow G`;;

let GROUP_ZPOW_SUBGROUP_GENERATED = `!G s:A->bool. group_zpow (subgroup_generated G s) = group_zpow G`;;

let GROUP_CONJUGATION_SUBGROUP_GENERATED = `!G s:A->bool.
    group_conjugation (subgroup_generated G s) = group_conjugation G`;;

let SUBGROUP_GENERATED_RESTRICT = `!G s:A->bool.
        subgroup_generated G s =
        subgroup_generated G (group_carrier G INTER s)`;;

let SUBGROUP_SUBGROUP_GENERATED = `!G s:A->bool. group_carrier(subgroup_generated G s) subgroup_of G`;;

let SUBGROUP_GENERATED_MONO = `!G s t:A->bool.
        s SUBSET t
        ==> group_carrier(subgroup_generated G s) SUBSET
            group_carrier(subgroup_generated G t)`;;

let SUBGROUP_GENERATED_MINIMAL = `!G h s:A->bool.
        s SUBSET h /\ h subgroup_of G
        ==> group_carrier(subgroup_generated G s) SUBSET h`;;

let SUBGROUPS_GENERATED_EQ = `!G s t:A->bool.
        s SUBSET group_carrier(subgroup_generated G t) /\
        t SUBSET group_carrier(subgroup_generated G s)
        ==> subgroup_generated G s = subgroup_generated G t`;;

let SUBGROUP_GENERATED_INDUCT = `!G P s:A->bool.
        (!x. x IN group_carrier G /\ x IN s ==> P x) /\
        P(group_id G) /\
        (!x. P x ==> P(group_inv G x)) /\
        (!x y. P x /\ P y ==> P(group_mul G x y))
        ==> !x. x IN group_carrier(subgroup_generated G s) ==> P x`;;

let GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET = `!G h:A->bool.
        group_carrier (subgroup_generated G h) SUBSET group_carrier G`;;

let SUBGROUP_GENERATED_SUPERSET = `!G s:A->bool.
    subgroup_generated G s = G <=>
    group_carrier G SUBSET group_carrier(subgroup_generated G s)`;;

let SUBGROUP_OF_SUBGROUP_GENERATED_EQ = `!G h k:A->bool.
        h subgroup_of (subgroup_generated G k) <=>
        h subgroup_of G /\ h SUBSET group_carrier(subgroup_generated G k)`;;

let SUBGROUP_GENERATED_INDUCT_STRONG = `!G P s:A->bool.
        (!x. x IN group_carrier G /\ x IN s ==> P x) /\
        P (group_id G) /\
        (!x. x IN group_carrier G /\ P x ==> P (group_inv G x)) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G /\ P x /\ P y
               ==> P (group_mul G x y))
         ==> !x. x IN group_carrier (subgroup_generated G s) ==> P x`;;

let SUBGROUP_GENERATED_INDUCT_ALT = `!G P s:A->bool.
        P (group_id G) /\
        (!x. x IN group_carrier G /\ x IN s ==> P x /\ P(group_inv G x)) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G /\ P x /\ P y
               ==> P (group_mul G x y))
        ==> !x. x IN group_carrier (subgroup_generated G s) ==> P x`;;

let SUBGROUP_GENERATED_INDUCT_LEFT = `!G P s:A->bool.
        P (group_id G) /\
        (!x y. x IN group_carrier G /\ x IN s /\ y IN group_carrier G /\ P y
               ==> P (group_mul G x y) /\ P (group_mul G (group_inv G x) y))
        ==> !x. x IN group_carrier(subgroup_generated G s) ==> P x`;;

let FINITE_SUBGROUP_GENERATED = `!G s:A->bool.
        FINITE(group_carrier G)
        ==> FINITE(group_carrier(subgroup_generated G s))`;;

let CARD_LE_SUBGROUP_GENERATED = `!(G:A group) s (k:K->bool).
      INFINITE k /\ s <=_c k ==> group_carrier(subgroup_generated G s) <=_c k`;;

let COUNTABLE_SUBGROUP_GENERATED = `!G s:A->bool.
        COUNTABLE(group_carrier G) \/ COUNTABLE s
        ==> COUNTABLE(group_carrier(subgroup_generated G s))`;;

let SUBGROUP_GENERATED_SUBSET_CARRIER = `!G h:A->bool.
     group_carrier G INTER h SUBSET group_carrier(subgroup_generated G h)`;;

let SUBSET_CARRIER_SUBGROUP_GENERATED = `!G s t:A->bool.
        s SUBSET group_carrier G /\ s SUBSET t
        ==> s SUBSET group_carrier(subgroup_generated G t)`;;

let SUBGROUP_GENERATED_MINIMAL_EQ = `!G h s:A->bool.
        h subgroup_of G
        ==> (group_carrier (subgroup_generated G s) SUBSET h <=>
             group_carrier G INTER s SUBSET h)`;;

let CARRIER_SUBGROUP_GENERATED_SUBGROUP = `!G h:A->bool.
        h subgroup_of G ==> group_carrier (subgroup_generated G h) = h`;;

let SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ = `!G h k:A->bool.
        k subgroup_of G
        ==> (h subgroup_of (subgroup_generated G k) <=>
             h subgroup_of G /\ h SUBSET k)`;;

let SUBGROUP_GENERATED_GROUP_CARRIER = `!G:A group. subgroup_generated G (group_carrier G) = G`;;

let SUBGROUP_OF_SUBGROUP_GENERATED = `!G g h:A->bool.
        g subgroup_of G /\ g SUBSET h
        ==> g subgroup_of (subgroup_generated G h)`;;

let SUBGROUP_GENERATED_SUBSET_CARRIER_SUBSET = `!G s:A->bool.
        s SUBSET group_carrier G
        ==> s SUBSET group_carrier(subgroup_generated G s)`;;

let SUBGROUP_GENERATED_REFL = `!G s:A->bool. group_carrier G SUBSET s ==> subgroup_generated G s = G`;;

let SUBGROUP_GENERATED_INC = `!G s x:A.
        s SUBSET group_carrier G /\ x IN s
        ==> x IN group_carrier(subgroup_generated G s)`;;

let SUBGROUP_GENERATED_INC_GEN = `!G s x:A.
        x IN group_carrier G /\ x IN s
        ==> x IN group_carrier(subgroup_generated G s)`;;

let SUBGROUP_OF_SUBGROUP_GENERATED_REV = `!G g h:A->bool.
        g subgroup_of (subgroup_generated G h)
        ==> g subgroup_of G`;;

let TRIVIAL_GROUP_SUBGROUP_GENERATED = `!G s:A->bool.
        trivial_group G ==> trivial_group(subgroup_generated G s)`;;

let TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL = `!G s:A->bool.
        s SUBSET {group_id G} ==> trivial_group(subgroup_generated G s)`;;

let TRIVIAL_GROUP_SUBGROUP_GENERATED_EQ = `!G s:A->bool.
        trivial_group(subgroup_generated G s) <=>
        group_carrier G INTER s SUBSET {group_id G}`;;

let TRIVIAL_GROUP_GENERATED_BY_ANYTHING = `!G s:A->bool. trivial_group G ==> subgroup_generated G s = G`;;

let SUBGROUP_GENERATED_BY_SUBGROUP_GENERATED = `!G s:A->bool.
        subgroup_generated G (group_carrier(subgroup_generated G s)) =
        subgroup_generated G s`;;

let SUBGROUP_GENERATED_INSERT_ID = `!G s:A->bool.
        subgroup_generated G (group_id G INSERT s) = subgroup_generated G s`;;

let GROUP_CARRIER_SUBGROUP_GENERATED_MONO = `!G s t:A->bool.
        group_carrier(subgroup_generated (subgroup_generated G s) t) SUBSET
        group_carrier(subgroup_generated G t)`;;

let SUBGROUP_GENERATED_IDEMPOT_GEN = `!G s t:A->bool.
        s SUBSET group_carrier(subgroup_generated G t)
        ==> subgroup_generated (subgroup_generated G t) s =
            subgroup_generated G s`;;

let SUBGROUP_GENERATED_IDEMPOT = `!G s t:A->bool.
        s SUBSET t
        ==> subgroup_generated (subgroup_generated G t) s =
            subgroup_generated G s`;;

let SUBGROUP_GENERATED_BY_SUBGROUP_GENERATED_IDEMPOT = `!G s t:A->bool.
        s SUBSET t
        ==> subgroup_generated (subgroup_generated G t)
                               (group_carrier (subgroup_generated G s)) =
            subgroup_generated G s`;;

let SUBGROUP_GENERATED_UNION_LEFT = `!G s t:A->bool.
        subgroup_generated G (group_carrier(subgroup_generated G s) UNION t) =
        subgroup_generated G (s UNION t)`;;

let SUBGROUP_GENERATED_UNION_RIGHT = `!G s t:A->bool.
        subgroup_generated G (s UNION group_carrier(subgroup_generated G t)) =
        subgroup_generated G (s UNION t)`;;

let SUBGROUP_GENERATED_UNION = `!G s t:A->bool.
        subgroup_generated G (group_carrier(subgroup_generated G s) UNION
                              group_carrier(subgroup_generated G t)) =
        subgroup_generated G (s UNION t)`;;

let TRIVIAL_GROUP_SUBGROUP_GENERATED_EMPTY = `!G:A group. trivial_group(subgroup_generated G {})`;;

let SUBGROUP_OF_COMMUTING_ELEMENTS = `!G z:A.
        z IN group_carrier G
        ==> {x | x IN group_carrier G /\ group_mul G x z = group_mul G z x}
            subgroup_of G`;;

let GROUP_COMMUTES_SUBGROUP_GENERATED_EQ = `!G s z:A.
        z IN group_carrier G
        ==> ((!x. x IN group_carrier(subgroup_generated G s)
                  ==> group_mul G x z = group_mul G z x) <=>
             (!x. x IN group_carrier G /\ x IN s
                  ==> group_mul G x z = group_mul G z x))`;;

let GROUP_COMMUTES_SUBGROUP_GENERATED = `!G s z:A.
        (!x. x IN s ==> group_mul G x z = group_mul G z x) /\
        z IN group_carrier G
        ==> (!x. x IN group_carrier(subgroup_generated G s)
                 ==> group_mul G x z = group_mul G z x)`;;

let GROUP_COMMUTES_SUBGROUPS_GENERATED_EQ = `!G s t:A->bool.
        (!x y. x IN group_carrier(subgroup_generated G s) /\
               y IN group_carrier(subgroup_generated G t)
               ==> group_mul G x y = group_mul G y x) <=>
        (!x y. x IN group_carrier G /\ x IN s /\
               y IN group_carrier G /\ y IN t
               ==> group_mul G x y = group_mul G y x)`;;

let ABELIAN_GROUP_SUBGROUP_GENERATED_GEN = `!G s:A->bool.
        (!x y. x IN group_carrier G /\ x IN s /\
               y IN group_carrier G /\ y IN s
               ==> group_mul G x y = group_mul G y x)
        ==> abelian_group (subgroup_generated G s)`;;

(* ------------------------------------------------------------------------- *)
(* Direct products and sums.                                                 *)
(* ------------------------------------------------------------------------- *)

let prod_group = new_definition
 `prod_group (G:A group) (G':B group) =
        group((group_carrier G) CROSS (group_carrier G'),
              (group_id G,group_id G'),
              (\(x,x'). group_inv G x,group_inv G' x'),
              (\(x,x') (y,y'). group_mul G x y,group_mul G' x' y'))`;;

let PROD_GROUP = `(!(G:A group) (G':B group).
        group_carrier (prod_group G G') =
        (group_carrier G) CROSS (group_carrier G')) /\
   (!(G:A group) (G':B group).
        group_id (prod_group G G') = (group_id G,group_id G')) /\
   (!(G:A group) (G':B group).
        group_inv (prod_group G G') =
          \(x,x'). group_inv G x,group_inv G' x') /\
   (!(G:A group) (G':B group).
        group_mul (prod_group G G') =
          \(x,x') (y,y'). group_mul G x y,group_mul G' x' y')`;;

let GROUP_POW_PROD_GROUP = `!(G:A group) (H:B group) x y n.
        x IN group_carrier G /\ y IN group_carrier H
        ==> group_pow (prod_group G H) (x,y) n =
            (group_pow G x n,group_pow H y n)`;;

let GROUP_ZPOW_PROD_GROUP = `!(G:A group) (H:B group) x y n.
        x IN group_carrier G /\ y IN group_carrier H
        ==> group_zpow (prod_group G H) (x,y) n =
            (group_zpow G x n,group_zpow H y n)`;;

let OPPOSITE_PROD_GROUP = `!(G1:A group) (G2:B group).
        opposite_group(prod_group G1 G2) =
        prod_group (opposite_group G1) (opposite_group G2)`;;

let TRIVIAL_PROD_GROUP = `!(G:A group) (H:B group).
        trivial_group(prod_group G H) <=>
        trivial_group G /\ trivial_group H`;;

let FINITE_PROD_GROUP = `!(G:A group) (H:B group).
        FINITE(group_carrier(prod_group G H)) <=>
        FINITE(group_carrier G) /\ FINITE(group_carrier H)`;;

let ABELIAN_PROD_GROUP = `!(G:A group) (H:B group).
        abelian_group(prod_group G H) <=>
        abelian_group G /\ abelian_group H`;;

let CROSS_SUBGROUP_OF_PROD_GROUP = `!(G1:A group) (G2:B group) h1 h2.
        (h1 CROSS h2) subgroup_of (prod_group G1 G2) <=>
        h1 subgroup_of G1 /\ h2 subgroup_of G2`;;

let PROD_GROUP_SUBGROUP_GENERATED = `!(G1:A group) (G2:B group) h1 h2.
        h1 subgroup_of G1 /\ h2 subgroup_of G2
        ==> (prod_group (subgroup_generated G1 h1) (subgroup_generated G2 h2) =
             subgroup_generated (prod_group G1 G2) (h1 CROSS h2))`;;

let product_group = new_definition
 `product_group k (G:K->A group) =
        group(cartesian_product k (\i. group_carrier(G i)),
              RESTRICTION k (\i. group_id (G i)),
              (\x. RESTRICTION k (\i. group_inv (G i) (x i))),
              (\x y. RESTRICTION k (\i. group_mul (G i) (x i) (y i))))`;;

let PRODUCT_GROUP = `(!k (G:K->A group).
        group_carrier(product_group k G) =
          cartesian_product k (\i. group_carrier(G i))) /\
   (!k (G:K->A group).
        group_id (product_group k G) =
          RESTRICTION k (\i. group_id (G i))) /\
   (!k (G:K->A group).
        group_inv (product_group k G) =
          \x. RESTRICTION k (\i. group_inv (G i) (x i))) /\
   (!k (G:K->A group).
        group_mul (product_group k G) =
          (\x y. RESTRICTION k (\i. group_mul (G i) (x i) (y i))))`;;

let GROUP_POW_PRODUCT_GROUP = `!(G:K->A group) k x n.
        group_pow (product_group k G) x n =
        RESTRICTION k (\i. group_pow (G i) (x i) n)`;;

let GROUP_ZPOW_PRODUCT_GROUP = `!(G:K->A group) k x n.
        group_zpow (product_group k G) x n =
        RESTRICTION k (\i. group_zpow (G i) (x i) n)`;;

let OPPOSITE_PRODUCT_GROUP = `!(G:K->A group) k.
        opposite_group(product_group k G) =
        product_group k (\i. opposite_group(G i))`;;

let GROUP_PRODUCT_INJECTION = `!k (G:K->A group) a i.
        RESTRICTION k (\j. if j = i then a else group_id (G j)) IN
        group_carrier(product_group k G) <=>
        i IN k ==> a IN group_carrier(G i)`;;

let TRIVIAL_PRODUCT_GROUP = `!k (G:K->A group).
        trivial_group(product_group k G) <=>
        !i. i IN k ==> trivial_group(G i)`;;

let CARTESIAN_PRODUCT_SUBGROUP_OF_PRODUCT_GROUP = `!k h G:K->A group.
        (cartesian_product k h) subgroup_of (product_group k G) <=>
        !i. i IN k ==> (h i) subgroup_of (G i)`;;

let PRODUCT_GROUP_SUBGROUP_GENERATED = `!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of (G i))
        ==> product_group k (\i. subgroup_generated (G i) (h i)) =
            subgroup_generated (product_group k G) (cartesian_product k h)`;;

let FINITE_PRODUCT_GROUP = `!k (G:K->A group).
        FINITE(group_carrier(product_group k G)) <=>
        FINITE {i | i IN k /\ ~trivial_group(G i)} /\
        !i. i IN k ==> FINITE(group_carrier(G i))`;;

let ABELIAN_PRODUCT_GROUP = `!k (G:K->A group).
        abelian_group(product_group k G) <=>
        !i. i IN k ==> abelian_group(G i)`;;

let sum_group = new_definition
  `sum_group k (G:K->A group) =
        subgroup_generated
         (product_group k G)
         {x | x IN cartesian_product k (\i. group_carrier(G i)) /\
              FINITE {i | i IN k /\ ~(x i = group_id(G i))}}`;;

let SUM_GROUP_ALT = `!k (G:K->A group).
      sum_group k G =
      subgroup_generated (product_group k G)
                 {x | FINITE {i | i IN k /\ ~(x i = group_id (G i))}}`;;

let SUM_GROUP_EQ_PRODUCT_GROUP = `!k (G:K->A group). FINITE k ==> sum_group k G = product_group k G`;;

let SUBGROUP_SUM_GROUP = `!k (G:K->A group).
    {x | x IN cartesian_product k (\i. group_carrier(G i)) /\
         FINITE {i | i IN k /\ ~(x i = group_id(G i))}}
    subgroup_of product_group k G`;;

let SUM_GROUP_CLAUSES = `(!k (G:K->A group).
        group_carrier(sum_group k G) =
          {x | x IN cartesian_product k (\i. group_carrier(G i)) /\
               FINITE {i | i IN k /\ ~(x i = group_id(G i))}}) /\
   (!k (G:K->A group).
        group_id (sum_group k G) =
          RESTRICTION k (\i. group_id (G i))) /\
   (!k (G:K->A group).
        group_inv (sum_group k G) =
          \x. RESTRICTION k (\i. group_inv (G i) (x i))) /\
   (!k (G:K->A group).
        group_mul (sum_group k G) =
          (\x y. RESTRICTION k (\i. group_mul (G i) (x i) (y i))))`;;

let GROUP_POW_SUM_GROUP = `!(G:K->A group) k x n.
        group_pow (sum_group k G) x n =
        RESTRICTION k (\i. group_pow (G i) (x i) n)`;;

let GROUP_ZPOW_SUM_GROUP = `!(G:K->A group) k x n.
        group_zpow (sum_group k G) x n =
        RESTRICTION k (\i. group_zpow (G i) (x i) n)`;;

let GROUP_SUM_INJECTION = `!k (G:K->A group) a i.
        RESTRICTION k (\j. if j = i then a else group_id (G j)) IN
        group_carrier(sum_group k G) <=>
        i IN k ==> a IN group_carrier(G i)`;;

let TRIVIAL_SUM_GROUP = `!k (G:K->A group).
        trivial_group(sum_group k G) <=> !i. i IN k ==> trivial_group(G i)`;;

let CARTESIAN_PRODUCT_SUBGROUP_OF_SUM_GROUP = `!k h G:K->A group.
        (cartesian_product k h) subgroup_of (sum_group k G) <=>
        (!i. i IN k ==> (h i) subgroup_of (G i)) /\
        (!z. z IN cartesian_product k h
             ==> FINITE {i | i IN k /\ ~(z i = group_id(G i))})`;;

let SUM_GROUP_SUBGROUP_GENERATED = `!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of (G i))
        ==> sum_group k (\i. subgroup_generated (G i) (h i)) =
            subgroup_generated (sum_group k G) (cartesian_product k h)`;;

let ABELIAN_SUM_GROUP = `!k (G:K->A group).
           abelian_group (sum_group k G) <=>
           (!i. i IN k ==> abelian_group (G i))`;;

(* ------------------------------------------------------------------------- *)
(* Homomorphisms etc.                                                        *)
(* ------------------------------------------------------------------------- *)

let group_homomorphism = new_definition
 `group_homomorphism (G,G') (f:A->B) <=>
        IMAGE f (group_carrier G) SUBSET group_carrier G' /\
        f (group_id G) = group_id G' /\
        (!x. x IN group_carrier G
             ==> f(group_inv G x) = group_inv G' (f x)) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> f(group_mul G x y) = group_mul G' (f x) (f y))`;;

let group_monomorphism = new_definition
 `group_monomorphism (G,G') (f:A->B) <=>
        group_homomorphism (G,G') f /\
        !x y. x IN group_carrier G /\ y IN group_carrier G /\ f x = f y
             ==> x = y`;;

let group_epimorphism = new_definition
 `group_epimorphism (G,G') (f:A->B) <=>
        group_homomorphism (G,G') f /\
        IMAGE f (group_carrier G) = group_carrier G'`;;

let group_endomorphism = new_definition
 `group_endomorphism G (f:A->A) <=> group_homomorphism (G,G) f`;;

let group_isomorphisms = new_definition
 `group_isomorphisms (G,G') ((f:A->B),g) <=>
        group_homomorphism (G,G') f /\
        group_homomorphism (G',G) g /\
        (!x. x IN group_carrier G ==> g(f x) = x) /\
        (!y. y IN group_carrier G' ==> f(g y) = y)`;;

let group_isomorphism = new_definition
 `group_isomorphism (G,G') (f:A->B) <=> ?g. group_isomorphisms (G,G') (f,g)`;;

let group_automorphism = new_definition
 `group_automorphism G (f:A->A) <=> group_isomorphism (G,G) f`;;

let GROUP_HOMOMORPHISM_EQ = `!G H (f:A->B) f'.
        group_homomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_homomorphism (G,H) f'`;;

let GROUP_MONOMORPHISM_EQ = `!G H (f:A->B) f'.
        group_monomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_monomorphism (G,H) f'`;;

let GROUP_EPIMORPHISM_EQ = `!G H (f:A->B) f'.
        group_epimorphism(G,H) f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_epimorphism (G,H) f'`;;

let GROUP_ENDOMORPHISM_EQ = `!G (f:A->A) f'.
        group_endomorphism G f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_endomorphism G f'`;;

let GROUP_ISOMORPHISMS_EQ = `!G H (f:A->B) g.
        group_isomorphisms(G,H) (f,g) /\
        (!x. x IN group_carrier G ==> f' x = f x) /\
        (!y. y IN group_carrier H ==> g' y = g y)
        ==> group_isomorphisms(G,H) (f',g')`;;

let GROUP_ISOMORPHISM_EQ = `!G H (f:A->B) f'.
        group_isomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_isomorphism (G,H) f'`;;

let GROUP_AUTOMORPHISM_EQ = `!G (f:A->A) f'.
        group_automorphism G f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_automorphism G f'`;;

let GROUP_HOMOMORPHISMS_EQ_ON_GENERATORS = `!G H s (f:A->B) g.
        group_homomorphism(G,H) f /\
        group_homomorphism(G,H) g /\
        (!x. x IN group_carrier G /\ x IN s ==> f x = g x)
        ==> !x. x IN group_carrier(subgroup_generated G s) ==> f x = g x`;;

let GROUP_ISOMORPHISMS_SYM = `!G G' (f:A->B) g.
        group_isomorphisms (G,G') (f,g) <=> group_isomorphisms(G',G) (g,f)`;;

let GROUP_ISOMORPHISMS_IMP_ISOMORPHISM = `!(f:A->B) g G G'.
        group_isomorphisms (G,G') (f,g) ==> group_isomorphism (G,G') f`;;

let GROUP_ISOMORPHISMS_IMP_ISOMORPHISM_ALT = `!(f:A->B) g G G'.
        group_isomorphisms (G,G') (f,g) ==> group_isomorphism (G',G) g`;;

let GROUP_HOMOMORPHISM = `!G G' f:A->B.
        group_homomorphism (G,G') (f:A->B) <=>
        IMAGE f (group_carrier G) SUBSET group_carrier G' /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> f(group_mul G x y) = group_mul G' (f x) (f y))`;;

let GROUP_EPIMORPHISM_SUBSET = `!G G' (f:A->B).
        group_epimorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_carrier G' SUBSET IMAGE f (group_carrier G)`;;

let GROUP_ISOMORPHISMS = `!G H (f:A->B) g.
        group_isomorphisms(G,H) (f,g) <=>
        group_homomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> g(f x) = x) /\
        (!y. y IN group_carrier H ==> g y IN group_carrier G /\ f(g y) = y)`;;

let GROUP_HOMOMORPHISM_OF_ID = `!(f:A->B) G G'.
        group_homomorphism(G,G') f ==> f (group_id G) = group_id G'`;;

let GROUP_HOMOMORPHISM_INV = `!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> !x. x IN group_carrier G
                ==> f(group_inv G x) = group_inv G' (f x)`;;

let GROUP_HOMOMORPHISM_MUL = `!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> !x y. x IN group_carrier G /\ y IN group_carrier G
                  ==> f(group_mul G x y) = group_mul G' (f x) (f y)`;;

let GROUP_HOMOMORPHISM_DIV = `!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> !x y. x IN group_carrier G /\ y IN group_carrier G
                  ==> f(group_div G x y) = group_div G' (f x) (f y)`;;

let GROUP_HOMOMORPHISM_POW = `!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> !x n. x IN group_carrier G
                  ==> f(group_pow G x n) = group_pow G' (f x) n`;;

let GROUP_HOMOMORPHISM_ZPOW = `!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> !x n. x IN group_carrier G
                  ==> f(group_zpow G x n) = group_zpow G' (f x) n`;;

let GROUP_HOMOMORPHISM_TRIVIAL = `!G H. group_homomorphism (G,H) (\x. group_id H)`;;

let GROUP_HOMOMORPHISM_ID = `!G:A group. group_homomorphism (G,G) (\x. x)`;;

let GROUP_MONOMORPHISM_ID = `!G:A group. group_monomorphism (G,G) (\x. x)`;;

let GROUP_EPIMORPHISM_ID = `!G:A group. group_epimorphism (G,G) (\x. x)`;;

let GROUP_ISOMORPHISMS_ID = `!G:A group. group_isomorphisms (G,G) ((\x. x),(\x. x))`;;

let GROUP_ISOMORPHISM_ID = `!G:A group. group_isomorphism (G,G) (\x. x)`;;

let GROUP_HOMOMORPHISM_COMPOSE = `!G1 G2 G3 (f:A->B) (g:B->C).
        group_homomorphism(G1,G2) f /\ group_homomorphism(G2,G3) g
        ==> group_homomorphism(G1,G3) (g o f)`;;

let GROUP_MONOMORPHISM_COMPOSE = `!G1 G2 G3 (f:A->B) (g:B->C).
        group_monomorphism(G1,G2) f /\ group_monomorphism(G2,G3) g
        ==> group_monomorphism(G1,G3) (g o f)`;;

let GROUP_MONOMORPHISM_COMPOSE_REV = `!(f:A->B) (g:B->C) A B C.
        group_homomorphism(A,B) f /\ group_homomorphism(B,C) g /\
        group_monomorphism(A,C) (g o f)
        ==> group_monomorphism(A,B) f`;;

let GROUP_EPIMORPHISM_COMPOSE = `!G1 G2 G3 (f:A->B) (g:B->C).
        group_epimorphism(G1,G2) f /\ group_epimorphism(G2,G3) g
        ==> group_epimorphism(G1,G3) (g o f)`;;

let GROUP_EPIMORPHISM_COMPOSE_REV = `!(f:A->B) (g:B->C) A B C.
        group_homomorphism(A,B) f /\ group_homomorphism(B,C) g /\
        group_epimorphism(A,C) (g o f)
        ==> group_epimorphism(B,C) g`;;

let GROUP_MONOMORPHISM_LEFT_INVERTIBLE = `!G H (f:A->B) g.
        group_homomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> g(f x) = x)
        ==> group_monomorphism (G,H) f`;;

let GROUP_EPIMORPHISM_RIGHT_INVERTIBLE = `!G H (f:A->B) g.
        group_homomorphism(G,H) f /\
        group_homomorphism(H,G) g /\
        (!x. x IN group_carrier G ==> g(f x) = x)
        ==> group_epimorphism (H,G) g`;;

let GROUP_HOMOMORPHISM_INTO_SUBGROUP = `!G G' h (f:A->B).
        group_homomorphism (G,G') f /\ IMAGE f (group_carrier G) SUBSET h
        ==> group_homomorphism (G,subgroup_generated G' h) f`;;

let GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN = `!(f:A->B) G H s.
      group_homomorphism(G,subgroup_generated H s) f <=>
      group_homomorphism(G,H) f /\
      IMAGE f (group_carrier G) SUBSET group_carrier(subgroup_generated H s)`;;

let GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ = `!G G' h (f:A->B).
        h subgroup_of G'
        ==> (group_homomorphism (G,subgroup_generated G' h) f <=>
             group_homomorphism (G,G') f /\
             IMAGE f (group_carrier G) SUBSET h)`;;

let GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED = `!(f:A->B) G H s.
        group_homomorphism (G,H) f
        ==> group_homomorphism(subgroup_generated G s,H) f`;;

let GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS = `!G H g h (f:A->B).
      group_homomorphism(G,H) f /\ IMAGE f g SUBSET h
      ==> group_homomorphism(subgroup_generated G g,subgroup_generated H h) f`;;

let GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS_ALT = `!G H g h (f:A->B).
      group_homomorphism(G,H) f /\ IMAGE f (group_carrier G INTER g) SUBSET h
      ==> group_homomorphism(subgroup_generated G g,subgroup_generated H h) f`;;

let GROUP_MONOMORPHISM_FROM_SUBGROUP_GENERATED = `!(f:A->B) G H s.
        group_monomorphism (G,H) f
        ==> group_monomorphism(subgroup_generated G s,H) f`;;

let GROUP_MONOMORPHISM_BETWEEN_SUBGROUPS = `!G H s t (f:A->B).
      group_monomorphism(G,H) f /\ IMAGE f s SUBSET t
      ==> group_monomorphism(subgroup_generated G s,subgroup_generated H t) f`;;

let GROUP_MONOMORPHISM_INTO_SUPERGROUP = `!G G' t (f:A->B).
        group_monomorphism(G,subgroup_generated G' t) f
        ==> group_monomorphism(G,G') f`;;

let GROUP_HOMOMORPHISM_INCLUSION = `!G s:A->bool. group_homomorphism(subgroup_generated G s,G) (\x. x)`;;

let GROUP_MONOMORPHISM_INCLUSION = `!G s:A->bool. group_monomorphism(subgroup_generated G s,G) (\x. x)`;;

let SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE = `!G H (f:A->B) s.
        group_homomorphism(G,H) f /\ s SUBSET group_carrier G
        ==> group_carrier (subgroup_generated H (IMAGE f s)) =
            IMAGE f (group_carrier(subgroup_generated G s))`;;

let SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE_EQ = `!G H s t (f:A->B).
        group_homomorphism (G,H) f /\
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G /\
        subgroup_generated G s = subgroup_generated G t
        ==> subgroup_generated H (IMAGE f s) =
            subgroup_generated H (IMAGE f t)`;;

let SUBGROUP_GENERATED_BY_EPIMORPHIC_IMAGE = `!G H s (f:A->B).
        group_epimorphism (G,H) f /\
        s SUBSET group_carrier G /\
        subgroup_generated G s = G
        ==> subgroup_generated H (IMAGE f s) = H`;;

let GROUP_EPIMORPHISM_BETWEEN_SUBGROUPS = `!G H (f:A->B).
        group_homomorphism(G,H) f /\ s SUBSET group_carrier G
        ==> group_epimorphism(subgroup_generated G s,
                              subgroup_generated H (IMAGE f s)) f`;;

let GROUP_EPIMORPHISM_INTO_SUBGROUP_EQ_GEN = `!(f:A->B) G H s.
      group_epimorphism(G,subgroup_generated H s) f <=>
      group_homomorphism(G,H) f /\
      IMAGE f (group_carrier G) = group_carrier(subgroup_generated H s)`;;

let GROUP_EPIMORPHISM_INTO_SUBGROUP_EQ = `!G G' h (f:A->B).
        h subgroup_of G'
        ==> (group_epimorphism (G,subgroup_generated G' h) f <=>
             group_homomorphism (G,G') f /\
             IMAGE f (group_carrier G) = h)`;;

let GROUP_ISOMORPHISM = `!G G' f:A->B.
      group_isomorphism (G,G') (f:A->B) <=>
      group_homomorphism (G,G') f /\
      IMAGE f (group_carrier G) = group_carrier G' /\
      (!x y. x IN group_carrier G /\ y IN group_carrier G /\ f x = f y
             ==> x = y)`;;

let GROUP_ISOMORPHISM_SUBSET = `!G G' f:A->B.
      group_isomorphism (G,G') (f:A->B) <=>
      group_homomorphism (G,G') f /\
      (!z. z IN group_carrier G' ==> ?x. x IN group_carrier G /\ f x = z) /\
      (!x y. x IN group_carrier G /\ y IN group_carrier G /\ f x = f y
             ==> x = y)`;;

let SUBGROUP_OF_HOMOMORPHIC_IMAGE = `!G G' (f:A->B).
        group_homomorphism (G,G') f /\ h subgroup_of G
        ==> IMAGE f h subgroup_of G'`;;

let SUBGROUP_OF_HOMOMORPHIC_PREIMAGE = `!G H (f:A->B) h.
        group_homomorphism(G,H) f /\ h subgroup_of H
        ==> {x | x IN group_carrier G /\ f x IN h} subgroup_of G`;;

let SUBGROUP_OF_EPIMORPHIC_PREIMAGE = `!G H (f:A->B) h.
        group_epimorphism(G,H) f /\ h subgroup_of H
        ==> {x | x IN group_carrier G /\ f x IN h} subgroup_of G /\
            IMAGE f {x | x IN group_carrier G /\ f x IN h} = h`;;

let GROUP_MONOMORPHISM_EPIMORPHISM = `!G G' f:A->B.
        group_monomorphism (G,G') f /\ group_epimorphism (G,G') f <=>
        group_isomorphism (G,G') f`;;

let GROUP_ISOMORPHISM_EPIMORPHISM = `!G G' (f:A->B).
        group_isomorphism (G,G') f <=>
        group_epimorphism (G,G') f /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G /\ f x = f y
               ==> x = y)`;;

let SUBGROUP_MONOMORPHISM_EPIMORPHISM = `!G G' s (f:A->B).
        group_monomorphism(G,G') f /\
        group_epimorphism(G,subgroup_generated G' s) f <=>
        group_isomorphism(G,subgroup_generated G' s) f`;;

let GROUP_ISOMORPHISM_IMP_MONOMORPHISM = `!G G' (f:A->B).
        group_isomorphism (G,G') f ==> group_monomorphism (G,G') f`;;

let GROUP_ISOMORPHISM_IMP_EPIMORPHISM = `!G G' (f:A->B).
        group_isomorphism (G,G') f ==> group_epimorphism (G,G') f`;;

let GROUP_MONOMORPHISM_IMP_HOMOMORPHISM = `!(f:A->B) G H. group_monomorphism(G,H) f ==> group_homomorphism(G,H) f`;;

let GROUP_EPIMORPHISM_IMP_HOMOMORPHISM = `!(f:A->B) G H. group_epimorphism(G,H) f ==> group_homomorphism(G,H) f`;;

let GROUP_ISOMORPHISM_IMP_HOMOMORPHISM = `!(f:A->B) G H. group_isomorphism(G,H) f ==> group_homomorphism(G,H) f`;;

let GROUP_AUTOMORPHISM_IMP_ENDOMORPHISM = `!G (f:A->A). group_automorphism G f ==> group_endomorphism G f`;;

let GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE = `!G H (f:A->B).
        FINITE(group_carrier G) /\ FINITE(group_carrier H) /\
        CARD(group_carrier G) = CARD(group_carrier H)
        ==> (group_isomorphism(G,H) f <=> group_monomorphism(G,H) f)`;;

let GROUP_ISOMORPHISM_EQ_EPIMORPHISM_FINITE = `!G H (f:A->B).
        FINITE(group_carrier G) /\ FINITE(group_carrier H) /\
        CARD(group_carrier G) = CARD(group_carrier H)
        ==> (group_isomorphism(G,H) f <=> group_epimorphism(G,H) f)`;;

let GROUP_ISOMORPHISMS_CONJUGATION = `!G a:A.
        a IN group_carrier G
        ==> group_isomorphisms (G,G)
             (group_conjugation G a,group_conjugation G (group_inv G a))`;;

let GROUP_AUTOMORPHISM_CONJUGATION = `!G a:A.
        a IN group_carrier G ==> group_automorphism G (group_conjugation G a)`;;

let GROUP_ISOMORPHISM_CONJUGATION = `!G a:A. a IN group_carrier G
           ==> group_isomorphism (G,G) (group_conjugation G a)`;;

let GROUP_HOMOMORPHISM_CONJUGATION = `!G a:A. a IN group_carrier G
           ==> group_homomorphism (G,G) (group_conjugation G a)`;;

let CARD_LE_GROUP_MONOMORPHIC_IMAGE = `!G H (f:A->B).
        group_monomorphism(G,H) f ==> group_carrier G <=_c group_carrier H`;;

let CARD_LE_GROUP_EPIMORPHIC_IMAGE = `!G H (f:A->B).
        group_epimorphism(G,H) f ==> group_carrier H <=_c group_carrier G`;;

let CARD_EQ_GROUP_ISOMORPHIC_IMAGE = `!G H (f:A->B).
        group_isomorphism(G,H) f ==> group_carrier G =_c group_carrier H`;;

let FINITE_GROUP_MONOMORPHIC_PREIMAGE = `!G H (f:A->B).
        group_monomorphism(G,H) f /\ FINITE(group_carrier H)
        ==> FINITE(group_carrier G)`;;

let FINITE_GROUP_EPIMORPHIC_IMAGE = `!G H (f:A->B).
        group_epimorphism(G,H) f /\ FINITE(group_carrier G)
        ==> FINITE(group_carrier H)`;;

let CARD_EQ_GROUP_MONOMORPHIC_IMAGE = `!G H (f:A->B).
        group_monomorphism(G,H) f
        ==> IMAGE f (group_carrier G) =_c group_carrier G`;;

let GROUP_ISOMORPHISMS_BETWEEN_SUBGROUPS = `!G H g h (f:A->B) f'.
      group_isomorphisms(G,H) (f,f') /\
      IMAGE f g SUBSET h /\ IMAGE f' h SUBSET g
      ==> group_isomorphisms (subgroup_generated G g,subgroup_generated H h)
                             (f,f')`;;

let GROUP_ISOMORPHISMS_BETWEEN_SUBGROUPS_ALT = `!G H g h (f:A->B) f'.
      group_isomorphisms(G,H) (f,f') /\
      IMAGE f (group_carrier G INTER g) SUBSET h /\
      IMAGE f' (group_carrier H INTER h) SUBSET g
      ==> group_isomorphisms (subgroup_generated G g,subgroup_generated H h)
                             (f,f')`;;

let GROUP_ISOMORPHISM_BETWEEN_SUBGROUPS = `!G H g h (f:A->B).
      group_isomorphism(G,H) f /\ g SUBSET group_carrier G /\ IMAGE f g = h
      ==> group_isomorphism(subgroup_generated G g,subgroup_generated H h) f`;;

let GROUP_ISOMORPHISMS_COMPOSE = `!G1 G2 G3 (f1:A->B) (f2:B->C) g1 g2.
        group_isomorphisms(G1,G2) (f1,g1) /\ group_isomorphisms(G2,G3) (f2,g2)
        ==> group_isomorphisms(G1,G3) (f2 o f1,g1 o g2)`;;

let GROUP_ISOMORPHISM_COMPOSE = `!G1 G2 G3 (f:A->B) (g:B->C).
        group_isomorphism(G1,G2) f /\ group_isomorphism(G2,G3) g
        ==> group_isomorphism(G1,G3) (g o f)`;;

let GROUP_ISOMORPHISM_COMPOSE_REV = `!(f:A->B) (g:B->C) A B C.
        group_homomorphism(A,B) f /\ group_homomorphism(B,C) g /\
        group_isomorphism(A,C) (g o f)
        ==> group_monomorphism(A,B) f /\ group_epimorphism(B,C) g`;;

let GROUP_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV = `!(f:A->B) (g:B->C) A B C.
        group_epimorphism (A,B) f /\
        group_homomorphism (B,C) g /\
        group_isomorphism (A,C) (g o f)
        ==> group_isomorphism (A,B) f /\ group_isomorphism (B,C) g`;;

let GROUP_MONOMORPHISM_ISOMORPHISM_COMPOSE_REV = `!(f:A->B) (g:B->C) A B C.
        group_homomorphism (A,B) f /\
        group_monomorphism (B,C) g /\
        group_isomorphism (A,C) (g o f)
        ==> group_isomorphism (A,B) f /\ group_isomorphism (B,C) g`;;

let GROUP_ISOMORPHISM_INVERSE = `!(f:A->B) g G H.
        group_isomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> g(f x) = x)
        ==> group_isomorphism(H,G) g`;;

let GROUP_ISOMORPHISMS_OPPOSITE_GROUP = `!G:A group.
        group_isomorphisms(G,opposite_group G) (group_inv G,group_inv G)`;;

let GROUP_ISOMORPHISM_OPPOSITE_GROUP = `!G:A group.
        group_isomorphism(G,opposite_group G) (group_inv G)`;;

let GROUP_HOMOMORPHISM_FROM_TRIVIAL_GROUP = `!(f:A->B) G H.
        trivial_group G
        ==> (group_homomorphism(G,H) f <=> f(group_id G) = group_id H)`;;

let GROUP_MONOMORPHISM_FROM_TRIVIAL_GROUP = `!(f:A->B) G H.
        trivial_group G
        ==> (group_monomorphism (G,H) f <=> group_homomorphism (G,H) f)`;;

let GROUP_MONOMORPHISM_TO_TRIVIAL_GROUP = `!(f:A->B) G H.
        trivial_group H
        ==> (group_monomorphism (G,H) f <=>
             group_homomorphism (G,H) f /\ trivial_group G)`;;

let GROUP_EPIMORPHISM_FROM_TRIVIAL_GROUP = `!(f:A->B) G H.
        trivial_group G
        ==> (group_epimorphism (G,H) f <=>
             group_homomorphism (G,H) f /\ trivial_group H)`;;

let GROUP_EPIMORPHISM_TO_TRIVIAL_GROUP = `!(f:A->B) G H.
        trivial_group H
        ==> (group_epimorphism (G,H) f <=>
             group_homomorphism (G,H) f)`;;

let GROUP_HOMOMORPHISM_PAIRWISE = `!(f:A->B#C) G H K.
        group_homomorphism(G,prod_group H K) f <=>
        group_homomorphism(G,H) (FST o f) /\
        group_homomorphism(G,K) (SND o f)`;;

let GROUP_HOMOMORPHISM_PAIRED = `!(f:A->B) (g:A->C) G H K.
        group_homomorphism(G,prod_group H K) (\x. f x,g x) <=>
        group_homomorphism(G,H) f /\
        group_homomorphism(G,K) g`;;

let GROUP_HOMOMORPHISM_PAIRED2 = `!(f:A->B) (g:C->D) G H G' H'.
        group_homomorphism(prod_group G H,prod_group G' H')
                (\(x,y). f x,g y) <=>
        group_homomorphism(G,G') f /\ group_homomorphism(H,H') g`;;

let GROUP_ISOMORPHISMS_PAIRED2 = `!(f:A->B) (g:C->D) f' g' G H G' H'.
        group_isomorphisms(prod_group G H,prod_group G' H')
                ((\(x,y). f x,g y),(\(x,y). f' x,g' y)) <=>
        group_isomorphisms(G,G') (f,f') /\
        group_isomorphisms(H,H') (g,g')`;;

let GROUP_ISOMORPHISM_PAIRED2 = `!(f:A->B) (g:C->D) G H G' H'.
        group_isomorphism(prod_group G H,prod_group G' H')
                (\(x,y). f x,g y) <=>
        group_isomorphism(G,G') f /\ group_isomorphism(H,H') g`;;

let GROUP_HOMOMORPHISM_OF_FST = `!(f:A->C) A (B:B group) C.
        group_homomorphism (prod_group A B,C) (f o FST) <=>
        group_homomorphism (A,C) f`;;

let GROUP_HOMOMORPHISM_OF_SND = `!(f:B->C) (A:A group) B C.
        group_homomorphism (prod_group A B,C) (f o SND) <=>
        group_homomorphism (B,C) f`;;

let GROUP_EPIMORPHISM_OF_FST = `!(f:A->C) A (B:B group) C.
        group_epimorphism (prod_group A B,C) (f o FST) <=>
        group_epimorphism (A,C) f`;;

let GROUP_EPIMORPHISM_OF_SND = `!(f:B->C) (A:A group) B C.
        group_epimorphism (prod_group A B,C) (f o SND) <=>
        group_epimorphism (B,C) f`;;

let GROUP_HOMOMORPHISM_FST = `!(A:A group) (B:B group). group_homomorphism (prod_group A B,A) FST`;;

let GROUP_HOMOMORPHISM_SND = `!(A:A group) (B:B group). group_homomorphism (prod_group A B,B) SND`;;

let GROUP_EPIMORPHISM_FST = `!(A:A group) (B:B group). group_epimorphism (prod_group A B,A) FST`;;

let GROUP_EPIMORPHISM_SND = `!(A:A group) (B:B group). group_epimorphism (prod_group A B,B) SND`;;

let GROUP_ISOMORPHISM_FST = `!(G:A group) (H:B group).
        group_isomorphism (prod_group G H,G) FST <=> trivial_group H`;;

let GROUP_ISOMORPHISM_SND = `!(G:A group) (H:B group).
        group_isomorphism (prod_group G H,H) SND <=> trivial_group G`;;

let GROUP_ISOMORPHISMS_PROD_GROUP_SWAP = `!(G:A group) (H:B group).
        group_isomorphisms (prod_group G H,prod_group H G)
                           ((\(x,y). y,x),(\(y,x). x,y))`;;

let GROUP_HOMOMORPHISM_COMPONENTWISE = `!G k H (f:A->K->B).
        group_homomorphism(G,product_group k H) f <=>
        IMAGE f (group_carrier G) SUBSET EXTENSIONAL k /\
        !i. i IN k ==> group_homomorphism (G,H i) (\x. f x i)`;;

let GROUP_HOMOMORPHISM_COMPONENTWISE_UNIV = `!G H (f:A->K->B).
        group_homomorphism(G,product_group (:K) H) f <=>
        !i. group_homomorphism (G,H i) (\x. f x i)`;;

let GROUP_HOMOMORPHISM_PRODUCT_PROJECTION = `!(G:K->A group) k i.
        i IN k ==> group_homomorphism (product_group k G,G i) (\x. x i)`;;

let GROUP_HOMOMORPHISM_SUM_PROJECTION = `!(G:K->A group) k i.
        i IN k ==> group_homomorphism (sum_group k G,G i) (\x. x i)`;;

let GROUP_HOMOMORPHISM_PRODUCT_INJECTION = `!k (G:K->A group) i.
        group_homomorphism
          (G i,product_group k G)
          (\a. RESTRICTION k (\j. if j = i then a else group_id(G j)))`;;

let GROUP_HOMOMORPHISM_SUM_INJECTION = `!k (G:K->A group) i.
        group_homomorphism
          (G i,sum_group k G)
          (\a. RESTRICTION k (\j. if j = i then a else group_id(G j)))`;;

let GROUP_HOMOMORPHISM_PRODUCT = `!(f:K->A->B) k G H.
        group_homomorphism (product_group k G,product_group k H)
                           (\x. RESTRICTION k (\i. (f i) (x i))) <=>
        !i. i IN k ==> group_homomorphism(G i,H i) (f i)`;;

let GROUP_HOMOMORPHISM_SUM = `!(f:K->A->B) k G H.
        group_homomorphism (sum_group k G,sum_group k H)
                           (\x. RESTRICTION k (\i. (f i) (x i))) <=>
        !i. i IN k ==> group_homomorphism(G i,H i) (f i)`;;

let GROUP_EPIMORPHISM_PRODUCT_PROJECTION = `!(G:K->A group) k i.
        i IN k ==> group_epimorphism (product_group k G,G i) (\x. x i)`;;

let GROUP_ISOMORPHISM_PRODUCT_PROJECTION = `!G k. group_isomorphism (product_group {k} G,G k) (\x. x k)`;;

let GROUP_EPIMORPHISM_SUM_PROJECTION = `!(G:K->A group) k i.
        i IN k ==> group_epimorphism (sum_group k G,G i) (\x. x i)`;;

let GROUP_ISOMORPHISM_SUM_PROJECTION = `!G k. group_isomorphism (sum_group {k} G,G k) (\x. x k)`;;

let ABELIAN_GROUP_EPIMORPHIC_IMAGE = `!G H (f:A->B).
     group_epimorphism(G,H) f /\ abelian_group G ==> abelian_group H`;;

let ABELIAN_GROUP_HOMOMORPHISM_GROUP_MUL = `!(f:A->B) g A B.
        abelian_group B /\
        group_homomorphism(A,B) f /\ group_homomorphism(A,B) g
        ==> group_homomorphism(A,B) (\x. group_mul B (f x) (g x))`;;

let ABELIAN_GROUP_HOMOMORPHISM_INVERSION = `!G:A group. group_homomorphism (G,G) (group_inv G) <=> abelian_group G`;;

let ABELIAN_GROUP_ISOMORPHISMS_INVERSION = `!G:A group. group_isomorphisms (G,G) (group_inv G,group_inv G) <=>
               abelian_group G`;;

let ABELIAN_GROUP_ISOMORPHISM_INVERSION = `!G:A group. group_isomorphism (G,G) (group_inv G) <=> abelian_group G`;;

let ABELIAN_GROUP_MONOMORPHISM_INVERSION = `!G:A group. group_monomorphism (G,G) (group_inv G) <=> abelian_group G`;;

let ABELIAN_GROUP_EPIMORPHISM_INVERSION = `!G:A group. group_epimorphism (G,G) (group_inv G) <=> abelian_group G`;;

let ABELIAN_GROUP_HOMOMORPHISM_POWERING = `!(G:A group) n.
        abelian_group G ==> group_homomorphism(G,G) (\x. group_pow G x n)`;;

let ABELIAN_GROUP_HOMOMORPHISM_ZPOWERING = `!(G:A group) n.
        abelian_group G ==> group_homomorphism(G,G) (\x. group_zpow G x n)`;;

(* ------------------------------------------------------------------------- *)
(* Relation of isomorphism.                                                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("isomorphic_group",(12, "right"));;

let isomorphic_group = new_definition
 `G isomorphic_group G' <=> ?f:A->B. group_isomorphism (G,G') f`;;

let GROUP_ISOMORPHISM_IMP_ISOMORPHIC = `!G H f:A->B. group_isomorphism (G,H) f ==> G isomorphic_group H`;;

let ISOMORPHIC_PRODUCT_GROUP_SING = `!(G:K->A group) k. product_group {k} G isomorphic_group G k`;;

let ISOMORPHIC_SUM_GROUP_SING = `!(G:K->A group) k. sum_group {k} G isomorphic_group G k`;;

let ISOMORPHIC_GROUP_REFL = `!G:A group. G isomorphic_group G`;;

let ISOMORPHIC_GROUP_SYM = `!(G:A group) (H:B group). G isomorphic_group H <=> H isomorphic_group G`;;

let ISOMORPHIC_GROUP_TRANS = `!(G1:A group) (G2:B group) (G3:C group).
        G1 isomorphic_group G2 /\ G2 isomorphic_group G3
        ==> G1 isomorphic_group G3`;;

let ISOMORPHIC_GROUP_OPPOSITE_GROUP = `!G:A group. (opposite_group G) isomorphic_group G`;;

let ISOMORPHIC_GROUP_TRIVIALITY = `!(G:A group) (H:B group).
        G isomorphic_group H ==> (trivial_group G <=> trivial_group H)`;;

let ISOMORPHIC_TO_TRIVIAL_GROUP = `(!(G:A group) (H:B group).
        trivial_group G ==> (G isomorphic_group H <=> trivial_group H)) /\
   (!(G:A group) (H:B group).
        trivial_group H ==> (G isomorphic_group H <=> trivial_group G))`;;

let ISOMORPHIC_TRIVIAL_GROUPS = `!(G:A group) (H:B group).
        trivial_group G /\ trivial_group H
        ==> G isomorphic_group H`;;

let ISOMORPHIC_GROUP_SINGLETON_GROUP = `(!(G:A group) (b:B).
        G isomorphic_group singleton_group b <=> trivial_group G) /\
   (!a:A (G:B group).
        singleton_group a isomorphic_group G <=> trivial_group G)`;;

let ISOMORPHIC_GROUP_PROD_GROUPS = `!(G:A group) (G':B group) (H:C group) (H':D group).
        G isomorphic_group G' /\ H isomorphic_group H'
        ==> (prod_group G H) isomorphic_group (prod_group G' H')`;;

let ISOMORPHIC_GROUP_PROD_GROUP_SYM = `!(G:A group) (H:B group).
        prod_group G H isomorphic_group prod_group H G`;;

let ISOMORPHIC_GROUP_PROD_GROUP_SWAP_LEFT = `!(G:A group) (H:B group) (K:C group).
        prod_group G H isomorphic_group K <=>
        prod_group H G isomorphic_group K`;;

let ISOMORPHIC_GROUP_PROD_GROUP_SWAP_RIGHT = `!(G:A group) (H:B group) (K:C group).
        G isomorphic_group prod_group H K <=>
        G isomorphic_group prod_group K H`;;

let ISOMORPHIC_PROD_TRIVIAL_GROUP = `(!(G:A group) (H:B group).
        trivial_group G ==> (prod_group G H isomorphic_group H)) /\
   (!(G:A group) (H:B group).
        trivial_group H ==> (prod_group G H isomorphic_group G)) /\
   (!(G:A group) (H:B group).
        trivial_group G ==> (H isomorphic_group prod_group G H)) /\
   (!(G:A group) (H:B group).
        trivial_group H ==> (G isomorphic_group prod_group G H))`;;

let ISOMORPHIC_PRODUCT_GROUP_SUPPORT = `!k (G:K->A group).
        product_group {i | i IN k /\ ~trivial_group(G i)} G isomorphic_group
        product_group k G`;;

let ISOMORPHIC_PRODUCT_GROUP_SYMDIFF = `!k l (G:K->A group).
        (!i. i IN (k DIFF l) UNION (l DIFF k) ==> trivial_group(G i))
        ==> product_group k G isomorphic_group product_group l G`;;

let ISOMORPHIC_SUM_GROUP_SUPPORT = `!k (G:K->A group).
        sum_group {i | i IN k /\ ~trivial_group(G i)} G isomorphic_group
        sum_group k G`;;

let ISOMORPHIC_SUM_GROUP_SYMDIFF = `!k l (G:K->A group).
        (!i. i IN (k DIFF l) UNION (l DIFF k) ==> trivial_group(G i))
        ==> sum_group k G isomorphic_group sum_group l G`;;

let ISOMORPHIC_PRODUCT_GROUP_BIJECTIONS,ISOMORPHIC_SUM_GROUP_BIJECTIONS =
 (CONJ_PAIR o prove)
 (`(!s (G:K->A group) t (H:L->B group) f g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y) /\
        (!i. i IN s ==> (G i) isomorphic_group H(f i))
        ==> product_group s G isomorphic_group product_group t H) /\
   (!s (G:K->A group) t (H:L->B group) f g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y) /\
        (!i. i IN s ==> (G i) isomorphic_group H(f i))
        ==> sum_group s G isomorphic_group sum_group t H)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[isomorphic_group; group_isomorphism] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:K->A->B`; `k:K->B->A`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [group_isomorphisms; FORALL_AND_THM;
    TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\(x:K->A). RESTRICTION t (\j:L. (h:K->A->B) (g j) (x (g j)))`;
    `\(y:L->B). RESTRICTION s (\i:K. (k:K->B->A) i (y (f i)))`] THEN
  REWRITE_TAC[SUM_GROUP_ALT] THENL
   [ALL_TAC;
    MATCH_MP_TAC GROUP_ISOMORPHISMS_BETWEEN_SUBGROUPS_ALT THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[GSYM NOT_IMP; RESTRICTION] THEN
      REWRITE_TAC[NOT_IMP; IN_INTER; PRODUCT_GROUP] THEN
      REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
      CONJ_TAC THENL [X_GEN_TAC `x:K->A`; X_GEN_TAC `y:L->B`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      MATCH_MP_TAC(MESON[FINITE_IMAGE; FINITE_SUBSET]
       `!f. t SUBSET IMAGE f s ==> FINITE s ==> FINITE t`)
      THENL [EXISTS_TAC `f:K->L`; EXISTS_TAC `g:L->K`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN
      ASM SET_TAC[]]] THEN
 (REWRITE_TAC[group_isomorphisms] THEN
  REWRITE_TAC[RESTRICTION_EXTENSION; PRODUCT_GROUP; FORALL_IN_GSPEC;
    IMP_CONJ; SUM_GROUP_CLAUSES; CARTESIAN_PRODUCT_AS_RESTRICTIONS] THEN
  ASM_SIMP_TAC[RESTRICTION] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_COMPONENTWISE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PRODUCT_GROUP] THEN
  REWRITE_TAC[RESTRICTION_IN_EXTENSIONAL] THEN SIMP_TAC[RESTRICTION] THEN
  CONJ_TAC THENL [X_GEN_TAC `j:L`; X_GEN_TAC `i:K`] THEN
  DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC GROUP_HOMOMORPHISM_COMPOSE THENL
   [EXISTS_TAC `(G:K->A group) (g(j:L))`;
    EXISTS_TAC `(H:L->B group) (f(i:K))`] THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_PRODUCT_PROJECTION] THEN
  ASM_MESON_TAC[]));;

let ISOMORPHIC_GROUP_PRODUCT_GROUP = `!(G:K->A group) (H:K->B group) k.
        (!i. i IN k ==> (G i) isomorphic_group (H i))
        ==> (product_group k G) isomorphic_group (product_group k H)`;;

let ISOMORPHIC_GROUP_SUM_GROUP = `!(G:K->A group) (H:K->B group) k.
        (!i. i IN k ==> (G i) isomorphic_group (H i))
        ==> (sum_group k G) isomorphic_group (sum_group k H)`;;

let GROUP_ISOMORPHISMS_PRODUCT_GROUP_DISJOINT_UNION = `!(f:K->A group) k l.
        DISJOINT k l
        ==> group_isomorphisms
                (product_group (k UNION l) f,
                 prod_group (product_group k f) (product_group l f))
                ((\f. RESTRICTION k f,RESTRICTION l f),
                 (\(f,g) x. if x IN k then f x else g x))`;;

let GROUP_ISOMORPHISMS_SUM_GROUP_DISJOINT_UNION = `!(f:K->A group) k l.
        DISJOINT k l
        ==> group_isomorphisms
                (sum_group (k UNION l) f,
                 prod_group (sum_group k f) (sum_group l f))
                ((\f. RESTRICTION k f,RESTRICTION l f),
                 (\(f,g) x. if x IN k then f x else g x))`;;

let GROUP_ISOMORPHISM_PRODUCT_GROUP_DISJOINT_UNION = `!(f:K->A group) k l.
        DISJOINT k l
        ==> group_isomorphism
                (product_group (k UNION l) f,
                 prod_group (product_group k f) (product_group l f))
                (\f. RESTRICTION k f,RESTRICTION l f)`;;

let GROUP_ISOMORPHISM_SUM_GROUP_DISJOINT_UNION = `!(f:K->A group) k l.
        DISJOINT k l
        ==> group_isomorphism
                (sum_group (k UNION l) f,
                 prod_group (sum_group k f) (sum_group l f))
                (\f. RESTRICTION k f,RESTRICTION l f)`;;

let ISOMORPHIC_PRODUCT_GROUP_DISJOINT_UNION = `!(f:K->A group) k l.
        DISJOINT k l
        ==> product_group (k UNION l) f isomorphic_group
            prod_group (product_group k f) (product_group l f)`;;

let ISOMORPHIC_SUM_GROUP_DISJOINT_UNION = `!(f:K->A group) k l.
        DISJOINT k l
        ==> sum_group (k UNION l) f isomorphic_group
            prod_group (sum_group k f) (sum_group l f)`;;

let ISOMORPHIC_PRODUCT_GROUP_INSERT = `!(f:K->A group) i k.
        ~(i IN k)
        ==> product_group (i INSERT k) f isomorphic_group
            prod_group (f i) (product_group k f)`;;

let ISOMORPHIC_SUM_GROUP_INSERT = `!(f:K->A group) i k.
        ~(i IN k)
        ==> sum_group (i INSERT k) f isomorphic_group
            prod_group (f i) (sum_group k f)`;;

let ISOMORPHIC_GROUP_CARD_EQ = `!(G:A group) (H:B group).
        G isomorphic_group H ==> group_carrier G =_c group_carrier H`;;

let ISOMORPHIC_GROUP_FINITENESS = `!(G:A group) (H:B group).
        G isomorphic_group H
        ==> (FINITE(group_carrier G) <=> FINITE(group_carrier H))`;;

let ISOMORPHIC_GROUP_INFINITENESS = `!(G:A group) (H:B group).
        G isomorphic_group H
        ==> (INFINITE(group_carrier G) <=> INFINITE(group_carrier H))`;;

let ISOMORPHIC_GROUP_HAS_ORDER = `!(G:A group) (H:B group) n.
        G isomorphic_group H
        ==> (group_carrier G HAS_SIZE n <=> group_carrier H HAS_SIZE n)`;;

let ISOMORPHIC_GROUP_ORDER = `!(G:A group) (H:B group).
        G isomorphic_group H /\
        (FINITE(group_carrier G) \/ FINITE(group_carrier H))
        ==> CARD(group_carrier G) = CARD(group_carrier H)`;;

let ISOMORPHIC_GROUP_ABELIANNESS = `!(G:A group) (H:B group).
        G isomorphic_group H ==> (abelian_group G <=> abelian_group H)`;;

let CREATE_ISOMORPHIC_COPY_OF_GROUP = `!(f:A->B) g G s z i m.
        z IN s /\
        (!x. x IN group_carrier G ==> f x IN s /\ g(f x) = x) /\
        (!y. y IN s ==> g y IN group_carrier G /\ f(g y) = y) /\
        g z = group_id G /\
        (!x. x IN s ==> i x = f(group_inv G (g x))) /\
        (!x y. x IN s /\ y IN s ==> m x y = f(group_mul G (g x) (g y)))
        ==> group_isomorphisms (G,group(s,z,i,m)) (f,g) /\
            group_carrier (group(s,z,i,m)) = s /\
            group_id (group(s,z,i,m)) = z /\
            group_inv (group(s,z,i,m)) = i /\
            group_mul (group(s,z,i,m)) = m`;;

let ISOMORPHIC_COPY_OF_GROUP = `!(G:A group) (s:B->bool).
        (?G'. group_carrier G' = s /\ G isomorphic_group G') <=>
        group_carrier G =_c s`;;

(* ------------------------------------------------------------------------- *)
(* Direct limits, in the special case where we are just using the            *)
(* inclusion map I as the monomorphism between rings in the directed family. *)
(* ------------------------------------------------------------------------- *)

let GROUP_DIRECT_LIMIT = `!c:(A group->bool).
        ~(c = {}) /\
        (!g g'. g IN c /\ g' IN c
                ==> ?G. G IN c /\
                        group_monomorphism(g,G) I /\
                        group_monomorphism(g',G) I)
        ==> ?G. group_carrier G = UNIONS {group_carrier g | g IN c} /\
                !g. g IN c ==> group_monomorphism(g,G) I`;;

(* ------------------------------------------------------------------------- *)
(* Perform group operations setwise.                                         *)
(* ------------------------------------------------------------------------- *)

let group_setinv = new_definition
 `group_setinv G g = {group_inv G x | x IN g}`;;

let group_setmul = new_definition
 `group_setmul G g h = {group_mul G x y | x IN g /\ y IN h}`;;

let GROUP_SETINV_AS_IMAGE = `!G:A group. group_setinv G = IMAGE (group_inv G)`;;

let SUBGROUP_OF_SETWISE = `!G s:A->bool.
        s subgroup_of G <=>
        s SUBSET group_carrier G /\
        group_id G IN s /\
        group_setinv G s SUBSET s /\
        group_setmul G s s SUBSET s`;;

let FINITE_SUBGROUP_OF_SETWISE = `!G s:A->bool.
        FINITE s
        ==> (s subgroup_of G <=>
             s SUBSET group_carrier G /\
             ~(s = {}) /\
             group_setmul G s s SUBSET s)`;;

let OPPOSITE_GROUP_SETINV = `!G s:A->bool.
        group_setinv (opposite_group G) s = group_setinv G s`;;

let OPPOSITE_GROUP_SETMUL = `!G s t:A->bool.
        group_setmul (opposite_group G) s t = group_setmul G t s`;;

let GROUP_SETINV_EQ_EMPTY = `!G g:A->bool. group_setinv G g = {} <=> g = {}`;;

let GROUP_SETMUL_EQ_EMPTY = `!G g h:A->bool. group_setmul G g h = {} <=> g = {} \/ h = {}`;;

let GROUP_SETMUL_EMPTY = `(!G s:A->bool. group_setmul G s {} = {}) /\
   (!G t:A->bool. group_setmul G {} t = {})`;;

let GROUP_SETINV_MONO = `!G s s':A->bool.
        s SUBSET s' ==> group_setinv G s SUBSET group_setinv G s'`;;

let GROUP_SETMUL_MONO = `!G s t s' t':A->bool.
        s SUBSET s' /\ t SUBSET t'
        ==> group_setmul G s t SUBSET group_setmul G s' t'`;;

let GROUP_SETMUL_INC_GEN = `(!G s t:A->bool.
        group_id G IN s /\ t SUBSET group_carrier G
        ==> t SUBSET group_setmul G s t) /\
   (!G s t:A->bool.
        s SUBSET group_carrier G /\ group_id G IN t
        ==> s SUBSET group_setmul G s t)`;;

let GROUP_SETMUL_INC = `(!G s t:A->bool.
        s subgroup_of G /\ t subgroup_of G ==> t SUBSET group_setmul G s t) /\
   (!G s t:A->bool.
        s subgroup_of G /\ t subgroup_of G ==> s SUBSET group_setmul G s t)`;;

let FINITE_GROUP_SETMUL = `!G s t:A->bool.
        FINITE s /\ FINITE t ==> FINITE(group_setmul G s t)`;;

let GROUP_SETMUL_SYM_ELEMENTWISE = `!G s t u:A->bool.
        (!a. a IN s ==> group_setmul G {a} t = group_setmul G u {a})
        ==> group_setmul G s t = group_setmul G u s`;;

let GROUP_SETINV_SING = `!G x:A. group_setinv G {x} = {group_inv G x}`;;

let GROUP_SETMUL_SING = `!G x y:A. group_setmul G {x} {y} = {group_mul G x y}`;;

let GROUP_SETINV = `!G g:A->bool.
        g SUBSET group_carrier G ==> group_setinv G g SUBSET group_carrier G`;;

let GROUP_SETMUL = `!G g h:A->bool.
        g SUBSET group_carrier G /\ h SUBSET group_carrier G==>
        group_setmul G g h SUBSET group_carrier G`;;

let GROUP_SETMUL_LID = `!G g:A->bool.
        g SUBSET group_carrier G ==> group_setmul G {group_id G} g = g`;;

let GROUP_SETMUL_RID = `!G g:A->bool.
        g SUBSET group_carrier G ==> group_setmul G g {group_id G} = g`;;

let GROUP_SETMUL_ASSOC = `!G g h i:A->bool.
        g SUBSET group_carrier G /\ h SUBSET group_carrier G /\
        i SUBSET group_carrier G
        ==> group_setmul G g (group_setmul G h i) =
            group_setmul G (group_setmul G g h) i`;;

let GROUP_SETMUL_SYM = `!G g h:A->bool.
        abelian_group G /\ g SUBSET group_carrier G /\ h SUBSET group_carrier G
        ==> group_setmul G g h = group_setmul G h g`;;

let GROUP_SETINV_SUBGROUP = `!G h:A->bool. h subgroup_of G ==> group_setinv G h = h`;;

let GROUP_SETMUL_LSUBSET = `!G h s:A->bool.
        h subgroup_of G /\ s SUBSET h /\ ~(s = {}) ==> group_setmul G s h = h`;;

let GROUP_SETMUL_RSUBSET = `!G h s:A->bool.
        h subgroup_of G /\ s SUBSET h /\ ~(s = {}) ==> group_setmul G h s = h`;;

let GROUP_SETMUL_LSUBSET_EQ = `!G h s:A->bool.
        h subgroup_of G /\ s SUBSET group_carrier G
        ==> (group_setmul G s h = h <=> s SUBSET h /\ ~(s = {}))`;;

let GROUP_SETMUL_RSUBSET_EQ = `!G h s:A->bool.
        h subgroup_of G /\ s SUBSET group_carrier G
        ==> (group_setmul G h s = h <=> s SUBSET h /\ ~(s = {}))`;;

let IMAGE_GROUP_CONJUGATION = `!G (a:A) s.
        IMAGE (group_conjugation G a) s =
        group_setmul G {a} (group_setmul G s {group_inv G a})`;;

let IMAGE_GROUP_CONJUGATION_EQ = `!G (a:A) s t.
        a IN group_carrier G /\
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G
        ==> (IMAGE (group_conjugation G a) s = t <=>
             group_setmul G {a} s = group_setmul G t {a})`;;

let GROUP_SETMUL_SUBGROUP = `!G h:A->bool.
        h subgroup_of G ==> group_setmul G h h = h`;;

let GROUP_SETMUL_LCANCEL = `!G g h x:A.
        x IN group_carrier G /\
        g SUBSET group_carrier G /\ h SUBSET group_carrier G
        ==> (group_setmul G {x} g = group_setmul G {x} h <=> g = h)`;;

let GROUP_SETMUL_RCANCEL = `!G g h x:A.
        x IN group_carrier G /\ g SUBSET group_carrier G /\
        h SUBSET group_carrier G
        ==> (group_setmul G g {x} = group_setmul G h {x} <=> g = h)`;;

let GROUP_SETMUL_LCANCEL_SET = `!G h x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\ h subgroup_of G
        ==> (group_setmul G h {x} = group_setmul G h {y} <=>
             group_div G x y IN h)`;;

let GROUP_SETMUL_RCANCEL_SET = `!G h x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\ h subgroup_of G
        ==> (group_setmul G {x} h = group_setmul G {y} h <=>
             group_mul G (group_inv G x) y IN h)`;;

let SUBGROUP_SETMUL_EQ = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> ((group_setmul G g h) subgroup_of G <=>
             group_setmul G g h = group_setmul G h g)`;;

let SUBGROUP_SETMUL = `!G g h:A->bool.
        abelian_group G /\ g subgroup_of G /\ h subgroup_of G
        ==> (group_setmul G g h) subgroup_of G`;;

let SUBGROUP_GENERATED_SETMUL = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> subgroup_generated G (group_setmul G g h) =
            subgroup_generated G (g UNION h)`;;

let CARRIER_SUBGROUP_GENERATED_UNION = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G /\
        group_setmul G g h = group_setmul G h g
        ==> group_carrier(subgroup_generated G (g UNION h)) =
            group_setmul G g h`;;

(* ------------------------------------------------------------------------- *)
(* Group actions.                                                            *)
(* ------------------------------------------------------------------------- *)

let group_action = new_definition
 `group_action G s (a:A->X->X) <=>
        (!g x. g IN group_carrier G /\ x IN s ==> a g x IN s) /\
        (!x. x IN s ==> a (group_id G) x = x) /\
        (!g h x. g IN group_carrier G /\ h IN group_carrier G /\ x IN s
                 ==> a (group_mul G g h) x = a g (a h x))`;;

let GROUP_ACTION_ALT = `!G s (a:A->X->X).
        group_action G s (a:A->X->X) <=>
        (!g x. g IN group_carrier G /\ x IN s ==> a g x IN s) /\
        (!x. x IN s ==> a (group_id G) x = x) /\
        (!g h x. g IN group_carrier G /\ h IN group_carrier G /\ x IN s
                 ==> a g (a h x) = a (group_mul G g h) x)`;;

let GROUP_ACTION_MUL = `!G s (a:A->X->X) g h x.
        group_action G s a /\
        g IN group_carrier G /\
        h IN group_carrier G /\
        x IN s
        ==> a g (a h x) = a (group_mul G g h) x`;;

let GROUP_ACTION_LINV = `!G s (a:A->X->X) g x.
        group_action G s a /\ g IN group_carrier G /\ x IN s
        ==> a (group_inv G g) (a g x) = x`;;

let GROUP_ACTION_RINV = `!G s (a:A->X->X) g x.
        group_action G s a /\ g IN group_carrier G /\ x IN s
        ==> a g (a (group_inv G g) x) = x`;;

let GROUP_ACTION_BIJECTIVE = `!G s (a:A->X->X) g.
        group_action G s a /\ g IN group_carrier G
        ==> !y. y IN s ==> ?!x. x IN s /\ a g x = y`;;

let GROUP_ACTION_SURJECTIVE = `!G s (a:A->X->X) g y.
        group_action G s a /\ g IN group_carrier G /\ y IN s
        ==> ?x. a g x = y`;;

let GROUP_ACTION_INJECTIVE = `!G s (a:A->X->X).
        group_action G s a /\ g IN group_carrier G /\ x IN s /\ y IN s
        ==> (a g x = a g y <=> x = y)`;;

let GROUP_ACTION_ON_SUBSET = `!G s t (a:A->X->X).
        group_action G s a /\
        t SUBSET s /\
        (!g x. g IN group_carrier G /\ x IN t ==> a g x IN t)
        ==> group_action G t a`;;

let GROUP_ACTION_FROM_SUBGROUP = `!G s h (a:A->X->X).
        group_action G s a ==> group_action (subgroup_generated G h) s a`;;

let GROUP_ACTIONS_EQ_ON_GENERATORS = time prove
 (`!G t s (a:A->X->X) a'.
        group_action G s a /\
        group_action G s a' /\
        (!g x. g IN group_carrier G /\ g IN t /\ x IN s ==> a g x = a' g x)
        ==> !g x. g IN group_carrier(subgroup_generated G t) /\ x IN s
                  ==> a g x = a' g x`,
  REWRITE_TAC[group_action] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC SUBGROUP_GENERATED_INDUCT_STRONG THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `g:A` THEN STRIP_TAC THEN
  X_GEN_TAC `x:X` THEN DISCH_TAC THEN MATCH_MP_TAC(MESON[]
   `!f:X->X.
        (!x y. x IN s /\ y IN s ==> (f x = f y <=> x = y)) /\
        g a IN s /\ h a IN s /\ f(g a) = a /\ f(h a) = a
        ==> g a = h a`) THEN
  EXISTS_TAC `(a:A->X->X) g` THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ACTION_INJECTIVE THEN
    MAP_EVERY EXISTS_TAC [`G:A group`; `s:X->bool`] THEN
    ASM_REWRITE_TAC[group_action];
    ASM_MESON_TAC[GROUP_ID; GROUP_MUL; GROUP_INV; GROUP_MUL_RINV]]);;

let GROUP_ACTION_IMAGE = `!G u s (a:A->X->X).
        group_action G s a /\
        (!t. t IN u ==> t SUBSET s) /\
        (!g t. g IN group_carrier G /\ t IN u ==> IMAGE (a g) t IN u)
        ==> group_action G u (IMAGE o a)`;;

let GROUP_ACTION_IMAGE_SIZED = `!G s k (a:A->X->X).
        group_action G s a
        ==> group_action G {t | t SUBSET s /\ t HAS_SIZE k} (IMAGE o a)`;;

let group_stabilizer = new_definition
 `group_stabilizer G (a:A->X->X) x = {g | g IN group_carrier G /\ a g x = x}`;;

let GROUP_STABILIZER_SUBSET_CARRIER = `!G a x. group_stabilizer G a x SUBSET group_carrier G`;;

let FINITE_GROUP_STABILIZER = `!G (a:A->X->X) x.
        FINITE(group_carrier G) ==> FINITE(group_stabilizer G a x)`;;

let SUBGROUP_OF_GROUP_STABILIZER = `!G s (a:A->X->X) x.
        group_action G s a /\ x IN s ==> group_stabilizer G a x subgroup_of G`;;

let GROUP_STABILIZER_NONEMPTY = `!G (a:A->X->X) s x.
        group_action G s a /\ x IN s ==> ~(group_stabilizer G a x = {})`;;

let GROUP_STABILIZER_SUBGROUP_GENERATED = `!G h (a:A->X->X) x.
        group_stabilizer (subgroup_generated G h) a x =
        group_carrier(subgroup_generated G h) INTER group_stabilizer G a x`;;

let GROUP_STABILIZER_ON_SUBGROUP = `!G h (a:A->X->X) x.
        h subgroup_of G
        ==> group_stabilizer (subgroup_generated G h) a x =
            h INTER group_stabilizer G a x`;;

let GROUP_ACTION_KERNEL_POINTWISE = `!G s (a:A->X->X).
        {g | g IN group_carrier G /\ !x. x IN s ==> a g x = x} =
        if s = {} then group_carrier G
        else INTERS {group_stabilizer G a x | x IN s}`;;

let GROUP_ACTION_EQ = `!G s (a:A->X->X) g h x.
        group_action G s a /\
        g IN group_carrier G /\ h IN group_carrier G /\
        x IN s
        ==> (a g x = a h x <=>
             group_mul G (group_inv G g) h IN group_stabilizer G a x)`;;

let GROUP_ACTION_FIBRES = `!G s (a:A->X->X) h x.
        group_action G s a /\ h IN group_carrier G /\ x IN s
        ==> {g | g IN group_carrier G /\ (a:A->X->X) g x = a h x} =
            IMAGE (group_mul G h) (group_stabilizer G a x)`;;

let group_orbit = new_definition
 `group_orbit G s (a:A->X->X) x y <=>
        x IN s /\ y IN s /\ ?g. g IN group_carrier G /\ a g x = y`;;

let GROUP_ORBIT_IN_SET = `!G s (a:A->X->X) x y.
        group_orbit G s a x y ==> x IN s /\ y IN s`;;

let IN_GROUP_ORBIT = `!G s (a:A->X->X) x y.
        y IN group_orbit G s a x <=>
        x IN s /\ y IN s /\ ?g. g IN group_carrier G /\ a g x = y`;;

let GROUP_ORBIT = `!G s (a:A->X->X) x.
        group_action G s a
        ==> group_orbit G s a x =
            if x IN s then {a g x | g IN group_carrier G} else {}`;;

let GROUP_ORBIT_SUBSET = `!G s (a:A->X->X) x. group_orbit G s a x SUBSET s`;;

let GROUP_ORBIT_ON_SUBSET = `!G s t (a:A->X->X).
        t SUBSET s /\ x IN t
        ==> group_orbit G t a x = t INTER group_orbit G s a x`;;

let FINITE_GROUP_ORBIT = `!G s (a:A->X->X) x.
        FINITE(group_carrier G) \/ FINITE s ==> FINITE(group_orbit G s a x)`;;

let GROUP_ORBIT_REFL_EQ = `!G s (a:A->X->X) x.
        group_action G s a ==> (group_orbit G s a x x <=> x IN s)`;;

let GROUP_ORBIT_REFL = `!G s (a:A->X->X) x.
        group_action G s a /\ x IN s
        ==> group_orbit G s a x x`;;

let IN_GROUP_ORBIT_SELF = `!G s (a:A->X->X) x.
        group_action G s a /\ x IN s ==> x IN group_orbit G s a x`;;

let GROUP_ORBIT_EMPTY = `!G s (a:A->X->X) x. ~(x IN s) ==> group_orbit G s a x = {}`;;

let GROUP_ORBIT_EQ_EMPTY = `!G s (a:A->X->X) x.
        group_action G s a
        ==> (group_orbit G s a x = {} <=> ~(x IN s))`;;

let GROUP_ORBIT_SYM_EQ = `!G s (a:A->X->X) x y.
        group_action G s a
        ==> (group_orbit G s a x y <=> group_orbit G s a y x)`;;

let GROUP_ORBIT_SYM = `!G s (a:A->X->X) x y.
        group_action G s a /\ group_orbit G s a x y
        ==> group_orbit G s a y x`;;

let GROUP_ORBIT_TRANS = `!G s (a:A->X->X) x y z.
        group_action G s a /\ group_orbit G s a x y /\ group_orbit G s a y z
        ==> group_orbit G s a x z`;;

let GROUP_ORBIT_EQ = `!G s (a:A->X->X) x y.
        group_action G s a /\ x IN s /\ y IN s
        ==> (group_orbit G s a x = group_orbit G s a y <=>
             group_orbit G s a x y)`;;

let CLOSED_GROUP_ORBIT = `!G s (a:A->X->X) x g.
        group_action G s a /\ g IN group_carrier G
        ==> IMAGE (a g) (group_orbit G s a x) SUBSET group_orbit G s a x`;;

let GROUP_ORBIT_EQ_SING = `!G s (a:A->X->X) x y.
        group_action G s a
        ==> (group_orbit G s a y = {x} <=>
             x IN s /\ y = x /\ !g. g IN group_carrier G ==> a g x = x)`;;

let GROUP_ORBIT_EQ_SING_SELF = `!G s (a:A->X->X) x.
        group_action G s a
        ==> (group_orbit G s a x = {x} <=>
             x IN s /\ !g. g IN group_carrier G ==> a g x = x)`;;

let GROUP_ORBIT_HAS_SIZE_1 = `!G s (a:A->X->X) x.
        group_action G s a
        ==> (group_orbit G s a x HAS_SIZE 1 <=>
             x IN s /\ !g. g IN group_carrier G ==> a g x = x)`;;

let GROUP_ACTION_INVARIANT_SUBSET = `!G s (a:A->X->X) t.
        group_action G s a /\ t SUBSET s
        ==> ((!g. g IN group_carrier G ==> IMAGE (a g) t SUBSET t) <=>
             (!g. g IN group_carrier G ==> IMAGE (a g) t = t))`;;

let GROUP_ACTION_CLOSED = `!G s (a:A->X->X) g.
        group_action G s a /\ g IN group_carrier G
        ==> IMAGE (a g) s SUBSET s`;;

let GROUP_ACTION_INVARIANT = `!G s (a:A->X->X) g.
        group_action G s a /\ g IN group_carrier G
        ==> IMAGE (a g) s = s`;;

let INVARIANT_GROUP_ORBIT = `!G s (a:A->X->X) x g.
        group_action G s a /\ g IN group_carrier G
        ==> IMAGE (a g) (group_orbit G s a x) = group_orbit G s a x`;;

let SUBSET_GROUP_ORBIT_CLOSED = `!G s (a:A->X->X) x t.
        group_action G s a /\ t SUBSET s /\
        (!g. g IN group_carrier G ==> IMAGE (a g) t SUBSET t)
        ==> (group_orbit G s a x SUBSET t <=>
             x IN s ==> ~DISJOINT (group_orbit G s a x) t)`;;

let SUBSET_GROUP_ORBIT_INVARIANT = `!G s (a:A->X->X) x t.
        group_action G s a /\ t SUBSET s /\
        (!g. g IN group_carrier G ==> IMAGE (a g) t = t)
        ==> (group_orbit G s a x SUBSET t <=>
             x IN s ==> ~DISJOINT (group_orbit G s a x) t)`;;

let GROUP_ORBITS_EQ = `!G s (a:A->X->X) x y.
        group_action G s a /\ x IN s /\ y IN s
        ==> (group_orbit G s a x = group_orbit G s a y <=>
             ~DISJOINT (group_orbit G s a x) (group_orbit G s a y))`;;

let DISJOINT_GROUP_ORBITS = `!G s (a:A->X->X) x y.
        group_action G s a /\ x IN s /\ y IN s
        ==> (DISJOINT (group_orbit G s a x) (group_orbit G s a y) <=>
             ~(group_orbit G s a x = group_orbit G s a y))`;;

let PAIRWISE_DISJOINT_GROUP_ORBITS = `!G s (a:A->X->X).
        group_action G s a
        ==> pairwise DISJOINT {group_orbit G s a x |x| x IN s}`;;

let UNIONS_GROUP_ORBITS_CLOSED = `!G s (a:A->X->X) t.
        group_action G s a /\ t SUBSET s /\
        (!g. g IN group_carrier G ==> IMAGE (a g) t SUBSET t)
        ==> UNIONS {group_orbit G s a x |x| x IN t} = t`;;

let UNIONS_GROUP_ORBITS_INVARIANT = `!G s (a:A->X->X) t.
        group_action G s a /\ t SUBSET s /\
        (!g. g IN group_carrier G ==> IMAGE (a g) t = t)
        ==> UNIONS {group_orbit G s a x |x| x IN t} = t`;;

let UNIONS_GROUP_ORBITS = `!G s (a:A->X->X).
        group_action G s a
        ==> UNIONS {group_orbit G s a x |x| x IN s} = s`;;

let NSUM_CARD_GROUP_ORBITS = `!G s (a:A->X->X).
        group_action G s a /\ FINITE s
        ==> nsum {group_orbit G s a x | x | x IN s} CARD = CARD s`;;

let ORBIT_STABILIZER_MUL_GEN = `!G s (a:A->X->X) x.
      group_action G s a /\ x IN s
      ==> group_orbit G s a x *_c group_stabilizer G a x =_c group_carrier G`;;

let ORBIT_STABILIZER_MUL = `!G s (a:A->X->X) x.
      FINITE(group_carrier G) /\ group_action G s a /\ x IN s
      ==> CARD(group_orbit G s a x) * CARD(group_stabilizer G a x) =
          CARD(group_carrier G)`;;

let CARD_GROUP_ORBIT_DIVIDES = `!G s (a:A->X->X) x.
        FINITE(group_carrier G) /\ group_action G s a /\ x IN s
        ==> CARD(group_orbit G s a x) divides CARD(group_carrier G)`;;

let CARD_GROUP_STABILIZER_DIVIDES = `!G s (a:A->X->X) x.
        FINITE(group_carrier G) /\ group_action G s a /\ x IN s
        ==> CARD(group_stabilizer G a x) divides CARD(group_carrier G)`;;

let GROUP_STABILIZER_OF_ACTION = `!G s (a:A->X->X) g x.
        group_action G s a /\ g IN group_carrier G /\ x IN s
        ==> group_stabilizer G a (a g x) =
            IMAGE (group_conjugation G g) (group_stabilizer G a x)`;;

let GROUP_ACTION_SUBGROUP_TRANSLATION = `!G (h:A->bool).
    group_action (subgroup_generated G h) (group_carrier G) (group_mul G)`;;

let GROUP_STABILIZER_SUBGROUP_TRANSLATION = `!G h a:A.
        h subgroup_of G /\ a IN group_carrier G
        ==> group_stabilizer (subgroup_generated G h) (group_mul G) a =
            {group_id G}`;;

let GROUP_ACTION_GROUP_TRANSLATION = `!G. group_action G (group_carrier G) (group_mul G)`;;

let GROUP_STABILIZER_GROUP_TRANSLATION = `!G a:A.
        a IN group_carrier G
        ==> group_stabilizer G (group_mul G) a = {group_id G}`;;

let GROUP_ACTION_SUBSET_TRANSLATION = `!(G:A group) u.
      (!s. s IN u ==> s SUBSET group_carrier G) /\
      (!a s. a IN group_carrier G /\ s IN u ==> IMAGE (group_mul G a) s IN u)
      ==> group_action G u (IMAGE o group_mul G)`;;

let GROUP_ACTION_CONJUGATION = `!G:A group. group_action G (group_carrier G) (group_conjugation G)`;;

let CARD_GROUP_SETMUL_GEN = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_setmul G g h) *_c (g INTER h) =_c g *_c h`;;

let CARD_GROUP_SETMUL_MUL = `!G g h:A->bool.
        FINITE g /\ FINITE h /\ g subgroup_of G /\ h subgroup_of G
        ==> CARD(group_setmul G g h) * CARD(g INTER h) = CARD g * CARD h`;;

let CARD_GROUP_SETMUL = `!G g h:A->bool.
        FINITE g /\ FINITE h /\ g subgroup_of G /\ h subgroup_of G
        ==> CARD(group_setmul G g h) = (CARD g * CARD h) DIV CARD(g INTER h)`;;

let CARD_GROUP_SETMUL_DIVIDES = `!G g h:A->bool.
        FINITE g /\ FINITE h /\ g subgroup_of G /\ h subgroup_of G
        ==> CARD(group_setmul G g h) divides CARD(g) * CARD(h)`;;

let GROUP_ORBIT_COMMON_DIVISOR = `!G s (a:A->X->X) n.
        group_action G s a /\
        FINITE s /\
        (!x. x IN s ==> n divides CARD(group_orbit G s a x))
        ==> n divides CARD s`;;

let GROUP_ORBIT_COMMON_INDEX = `!G s (a:A->X->X) p k.
        group_action G s a /\
        FINITE s /\ (s = {} ==> k = 0) /\
        (!x. x IN s ==> k <= index p (CARD(group_orbit G s a x)))
        ==> k <= index p (CARD s)`;;

(* ------------------------------------------------------------------------- *)
(* Right and left cosets.                                                    *)
(* ------------------------------------------------------------------------- *)

let right_coset = new_definition
 `right_coset G h x = group_setmul G h {x}`;;

let left_coset = new_definition
 `left_coset G x h = group_setmul G {x} h`;;

let LEFT_COSET_AS_IMAGE = `!(x:A) h. left_coset G x h = IMAGE (group_mul G x) h`;;

let RIGHT_COSET = `!G h x:A.
        x IN group_carrier G /\ h SUBSET group_carrier G
        ==> right_coset G h x SUBSET group_carrier G`;;

let LEFT_COSET = `!G h x:A.
        x IN group_carrier G /\ h SUBSET group_carrier G
        ==> left_coset G x h SUBSET group_carrier G`;;

let IN_RIGHT_COSET = `!G h x a:A.
        h SUBSET group_carrier G /\
        a IN group_carrier G /\ x IN group_carrier G
        ==> (x IN right_coset G h a <=>
             group_mul G x (group_inv G a) IN h)`;;

let IN_LEFT_COSET = `!G h x a:A.
        h SUBSET group_carrier G /\
        a IN group_carrier G /\ x IN group_carrier G
        ==> (x IN left_coset G a h <=>
             group_mul G (group_inv G a) x IN h)`;;

let IN_RIGHT_COSET_INV = `!G h x y:A.
        h SUBSET group_carrier G /\
        x IN group_carrier G /\ y IN group_carrier G
        ==> (x IN right_coset G h (group_inv G y) <=>
             group_mul G x y IN h)`;;

let IN_LEFT_COSET_INV = `!G h x y:A.
        h SUBSET group_carrier G /\
        x IN group_carrier G /\ y IN group_carrier G
        ==> (x IN left_coset G (group_inv G y) h <=>
             group_mul G y x IN h)`;;

let GROUP_SETINV_LEFT_COSET_GEN,GROUP_SETINV_RIGHT_COSET_GEN =
 (CONJ_PAIR o prove)
 (`(!G h a:A.
        h subgroup_of G /\ a IN group_carrier G
        ==> group_setinv G (left_coset G a h) =
            right_coset G h (group_inv G a)) /\
   (!G h a:A.
        h subgroup_of G /\ a IN group_carrier G
        ==> group_setinv G (right_coset G h a) =
            left_coset G (group_inv G a) h)`,
  REWRITE_TAC[GROUP_SETINV_AS_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM FORALL_IN_GROUP_CARRIER_INV] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; AND_FORALL_THM; IMP_IMP] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[GROUP_INV_INV] THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
   `!u. s SUBSET u /\ t SUBSET u /\ (!x. x IN u ==> f(f x) = x) /\
        (!x. x IN u ==> (f x IN t <=> x IN s)) /\
        (!x. x IN u ==> (f x IN s <=> x IN t))
        ==> IMAGE f s = t /\ IMAGE f t = s`) THEN
  EXISTS_TAC `group_carrier G:A->bool` THEN
  ASM_SIMP_TAC[IN_LEFT_COSET; IN_RIGHT_COSET; SUBGROUP_OF_IMP_SUBSET;
               GROUP_INV_INV; GROUP_INV; LEFT_COSET; RIGHT_COSET] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ISPEC `G:A group` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] IN_SUBGROUP_INV)) THEN
  ASM_SIMP_TAC[GROUP_INV_MUL; GROUP_INV_INV; GROUP_INV]);;

let RIGHT_COSET_OPPOSITE_GROUP = `!G h x:A. right_coset G h x = left_coset (opposite_group G) x h`;;

let LEFT_COSET_OPPOSITE_GROUP = `!G h x:A. left_coset G x h = right_coset (opposite_group G) h x`;;

let GROUP_CONJUGATION_RIGHT_COSET = `!G h x:A.
     x IN group_carrier G /\ h SUBSET group_carrier G
     ==> IMAGE (group_conjugation G x) (right_coset G h x) = left_coset G x h`;;

let RIGHT_COSET_GROUP_CONJUGATION = `!G h x:A.
     x IN group_carrier G /\ h SUBSET group_carrier G
     ==> right_coset G (IMAGE (group_conjugation G x) h) x =
         left_coset G x h`;;

let LEFT_COSET_LEFT_COSET = `!x y h:A->bool.
        x IN group_carrier G /\
        y IN group_carrier G /\
        h SUBSET group_carrier G
        ==> left_coset G x (left_coset G y h) =
            left_coset G (group_mul G x y) h`;;

let RIGHT_COSET_RIGHT_COSET = `!x y h:A->bool.
        h SUBSET group_carrier G /\
        x IN group_carrier G /\
        y IN group_carrier G
        ==> right_coset G (right_coset G h x) y =
            right_coset G h (group_mul G x y)`;;

let RIGHT_COSET_ID = `!G h:A->bool.
        h SUBSET group_carrier G ==> right_coset G h (group_id G) = h`;;

let LEFT_COSET_ID = `!G h:A->bool.
        h SUBSET group_carrier G ==> left_coset G (group_id G) h = h`;;

let LEFT_COSET_TRIVIAL = `!G x:A. x IN group_carrier G ==> left_coset G x {group_id G} = {x}`;;

let RIGHT_COSET_TRIVIAL = `!G x:A. x IN group_carrier G ==> right_coset G {group_id G} x = {x}`;;

let LEFT_COSET_CARRIER = `!G x:A. x IN group_carrier G
           ==> left_coset G x (group_carrier G) = group_carrier G`;;

let RIGHT_COSET_CARRIER = `!G x:A. x IN group_carrier G
           ==> right_coset G (group_carrier G) x = group_carrier G`;;

let RIGHT_COSET_EQ = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (right_coset G h x = right_coset G h y <=> group_div G x y IN h)`;;

let LEFT_COSET_EQ = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (left_coset G x h = left_coset G y h <=>
             group_mul G (group_inv G x) y IN h)`;;

let RIGHT_COSET_EQ_SUBGROUP = `!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (right_coset G h x = h <=> x IN h)`;;

let LEFT_COSET_EQ_SUBGROUP = `!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (left_coset G x h = h <=> x IN h)`;;

let RIGHT_COSET_EQ_EMPTY = `!G h x:A. right_coset G h x = {} <=> h = {}`;;

let LEFT_COSET_EQ_EMPTY = `!G h x:A. left_coset G x h = {} <=> h = {}`;;

let RIGHT_COSET_NONEMPTY = `!G h x:A. h subgroup_of G ==> ~(right_coset G h x = {})`;;

let LEFT_COSET_NONEMPTY = `!G h x:A. h subgroup_of G ==> ~(left_coset G x h = {})`;;

let IN_RIGHT_COSET_SELF = `!G h x:A.
      h subgroup_of G /\ x IN group_carrier G ==> x IN right_coset G h x`;;

let IN_LEFT_COSET_SELF = `!G h x:A.
      h subgroup_of G /\ x IN group_carrier G ==> x IN left_coset G x h`;;

let UNIONS_RIGHT_COSETS = `!G h:A->bool.
        h subgroup_of G
        ==> UNIONS {right_coset G h x |x| x IN group_carrier G} =
            group_carrier G`;;

let UNIONS_LEFT_COSETS = `!G h:A->bool.
        h subgroup_of G
        ==> UNIONS {left_coset G x h |x| x IN group_carrier G} =
            group_carrier G`;;

let RIGHT_COSETS_EQ = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (right_coset G h x = right_coset G h y <=>
             ~(DISJOINT (right_coset G h x) (right_coset G h y)))`;;

let LEFT_COSETS_EQ = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (left_coset G x h = left_coset G y h <=>
             ~(DISJOINT (left_coset G x h) (left_coset G y h)))`;;

let DISJOINT_RIGHT_COSETS = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (DISJOINT (right_coset G h x) (right_coset G h y) <=>
             ~(right_coset G h x = right_coset G h y))`;;

let DISJOINT_LEFT_COSETS = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (DISJOINT (left_coset G x h) (left_coset G y h) <=>
             ~(left_coset G x h = left_coset G y h))`;;

let PAIRWISE_DISJOINT_RIGHT_COSETS = `!G h:A->bool.
        h subgroup_of G
        ==> pairwise DISJOINT {right_coset G h a |a| a IN group_carrier G}`;;

let PAIRWISE_DISJOINT_LEFT_COSETS = `!G h:A->bool.
        h subgroup_of G
        ==> pairwise DISJOINT {left_coset G a h |a| a IN group_carrier G}`;;

let IMAGE_RIGHT_COSET_SWITCH = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> IMAGE (\a. group_mul G a (group_mul G (group_inv G x) y))
                  (right_coset G h x) =
            right_coset G h y`;;

let IMAGE_LEFT_COSET_SWITCH = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> IMAGE (\a. group_mul G (group_div G y x) a)
                  (left_coset G x h) =
            left_coset G y h`;;

let CARD_EQ_LEFT_RIGHT_COSETS = `!G h:A->bool.
        h subgroup_of G
        ==> {left_coset G x h |x| x IN group_carrier G} =_c
            {right_coset G h x |x| x IN group_carrier G}`;;

let HAS_SIZE_LEFT_RIGHT_COSETS = `!G h:A->bool.
        h subgroup_of G
        ==> ({left_coset G x h | x | x IN group_carrier G} HAS_SIZE n <=>
             {right_coset G h x | x | x IN group_carrier G} HAS_SIZE n)`;;

let CARD_EQ_RIGHT_COSETS = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> right_coset G h x =_c right_coset G h y`;;

let GROUP_ID_IN_LEFT_COSET_GEN = `!G h x:A.
        h SUBSET group_carrier G /\ x IN group_carrier G
        ==> (group_id G IN left_coset G x h <=> group_inv G x IN h)`;;

let GROUP_ID_IN_LEFT_COSET = `!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (group_id G IN left_coset G x h <=> x IN h)`;;

let SUBGROUP_OF_LEFT_COSET = `!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (left_coset G x h subgroup_of G <=> left_coset G x h = h)`;;

let GROUP_ID_IN_RIGHT_COSET_GEN = `!G h x:A.
        h SUBSET group_carrier G /\ x IN group_carrier G
        ==> (group_id G IN right_coset G h x <=> group_inv G x IN h)`;;

let GROUP_ID_IN_RIGHT_COSET = `!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (group_id G IN right_coset G h x <=> x IN h)`;;

let SUBGROUP_OF_RIGHT_COSET = `!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (right_coset G h x subgroup_of G <=> right_coset G h x = h)`;;

let CARD_EQ_LEFT_COSETS = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> left_coset G x h =_c left_coset G y h`;;

let CARD_EQ_RIGHT_COSET_SUBGROUP = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> right_coset G h x =_c h`;;

let CARD_EQ_LEFT_COSET_SUBGROUP = `!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> left_coset G x h =_c h`;;

let GROUP_ORBIT_SUBGROUP_TRANSLATION = `!G h a:A.
   h subgroup_of G /\ a IN group_carrier G
   ==> group_orbit (subgroup_generated G h) (group_carrier G) (group_mul G) a =
       right_coset G h a`;;

let GROUP_ORBIT_GROUP_TRANSLATION = `!G a:A.
    a IN group_carrier G
    ==> group_orbit G (group_carrier G) (group_mul G) a = group_carrier G`;;

let ORBIT_STABILIZER_GEN = `!G s (a:A->X->X) x.
      group_action G s a /\ x IN s
      ==> group_orbit G s a x =_c
          {left_coset G g (group_stabilizer G a x) |g| g IN group_carrier G}`;;

let ORBIT_STABILIZER = `!G s (a:A->X->X) x.
      FINITE(group_carrier G) /\ group_action G s a /\ x IN s
      ==> CARD (group_orbit G s a x) =
          CARD {left_coset G g (group_stabilizer G a x) |g|
                g IN group_carrier G}`;;

let GROUP_ACTION_LEFT_COSET_MULTIPLICATION = `!G h:A->bool.
        h SUBSET group_carrier G
        ==> group_action G {left_coset G x h | x | x IN group_carrier G}
                           (IMAGE o group_mul G)`;;

let GROUP_ORBIT_LEFT_COSET_MULTIPLICATION = `!G h a:A.
        a IN group_carrier G /\ h subgroup_of G
        ==> group_orbit G { left_coset G x h | x | x IN group_carrier G}
                          (IMAGE o group_mul G) (left_coset G a h) =
            { left_coset G x h | x | x IN group_carrier G}`;;

let GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION = `!G h a:A.
        a IN group_carrier G /\ h subgroup_of G
        ==> group_stabilizer G (IMAGE o group_mul G) (left_coset G a h) =
            IMAGE (group_conjugation G a) h`;;

let GROUP_ORBIT_LEFT_COSET_MULTIPLICATION_ID = `!G h:A->bool.
        h subgroup_of G
        ==> group_orbit G { left_coset G x h | x | x IN group_carrier G}
                          (IMAGE o group_mul G) h =
            { left_coset G x h | x | x IN group_carrier G}`;;

let GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION_ID = `!G h:A->bool.
        h subgroup_of G
        ==> group_stabilizer G (IMAGE o group_mul G) h = h`;;

let LAGRANGE_THEOREM_LEFT_GEN = `!G h:A->bool.
        h subgroup_of G
        ==> {left_coset G x h | x | x IN group_carrier G} *_c h =_c
            group_carrier G`;;

let LAGRANGE_THEOREM_RIGHT_GEN = `!G h:A->bool.
        h subgroup_of G
        ==> {right_coset G h x | x | x IN group_carrier G} *_c h =_c
            group_carrier G`;;

let LAGRANGE_THEOREM_LEFT = `!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {left_coset G x h |x| x IN group_carrier G} * CARD h =
            CARD(group_carrier G)`;;

let LAGRANGE_THEOREM_RIGHT = `!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {right_coset G h x |x| x IN group_carrier G} * CARD h =
            CARD(group_carrier G)`;;

let LAGRANGE_THEOREM = `!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> (CARD h) divides CARD(group_carrier G)`;;

let CARD_LEFT_COSETS_DIVIDES = `!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {left_coset G x h | x | x IN group_carrier G} divides
            CARD(group_carrier G)`;;

let CARD_RIGHT_COSETS_DIVIDES = `!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {right_coset G h x | x | x IN group_carrier G} divides
            CARD(group_carrier G)`;;

let LAGRANGE_THEOREM_LEFT_DIV = `!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {left_coset G x h | x | x IN group_carrier G} =
            CARD(group_carrier G) DIV CARD h`;;

let LAGRANGE_THEOREM_RIGHT_DIV = `!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {right_coset G h x | x | x IN group_carrier G} =
            CARD(group_carrier G) DIV CARD h`;;

let GROUP_SETMUL_PROD_GROUP = `!(G1:A group) (G2:B group) s1 s2 t1 t2.
        group_setmul (prod_group G1 G2) (s1 CROSS s2) (t1 CROSS t2) =
        (group_setmul G1 s1 t1) CROSS (group_setmul G2 s2 t2)`;;

let RIGHT_COSET_PROD_GROUP = `!G1 G2 h1 h2 (x1:A) (x2:B).
        right_coset (prod_group G1 G2) (h1 CROSS h2) (x1,x2) =
        (right_coset G1 h1 x1) CROSS (right_coset G2 h2 x2)`;;

let LEFT_COSET_PROD_GROUP = `!G1 G2 h1 h2 (x1:A) (x2:B).
        left_coset (prod_group G1 G2) (x1,x2) (h1 CROSS h2) =
        (left_coset G1 x1 h1) CROSS (left_coset G2 x2 h2)`;;

let GROUP_SETMUL_PRODUCT_GROUP = `!(G:K->A group) k s t.
        group_setmul (product_group k G)
                     (cartesian_product k s) (cartesian_product k t) =
        cartesian_product k (\i. group_setmul (G i) (s i) (t i))`;;

let RIGHT_COSET_PRODUCT_GROUP = `!(G:K->A group) h x k.
        right_coset (product_group k G) (cartesian_product k h) x =
        cartesian_product k (\i. right_coset (G i) (h i) (x i))`;;

let LEFT_COSET_PRODUCT_GROUP = `!(G:K->A group) h x k.
        left_coset (product_group k G) x (cartesian_product k h) =
        cartesian_product k (\i. left_coset (G i) (x i) (h i))`;;

let GROUP_SETINV_SUBGROUP_GENERATED = `!G h:A->bool.
        group_setinv (subgroup_generated G h) = group_setinv G`;;

let GROUP_SETMUL_SUBGROUP_GENERATED = `!G h:A->bool.
        group_setmul (subgroup_generated G h) = group_setmul G`;;

let RIGHT_COSET_SUBGROUP_GENERATED = `!G h k x. right_coset (subgroup_generated G h) k x = right_coset G k x`;;

let LEFT_COSET_SUBGROUP_GENERATED = `!G h k x. left_coset (subgroup_generated G h) x k = left_coset G x k`;;

let SCHREIER_TRANSVERSAL_LEMMA = `!(G:A group) h s t.
      h subgroup_of G /\
      s SUBSET group_carrier G /\
      subgroup_generated G s = G /\
      (!x. x IN s ==> group_inv G x IN s) /\
      t SUBSET group_carrier G /\
      UNIONS {right_coset G h x | x IN t} = group_carrier G /\
      t INTER h SUBSET {group_id G}
      ==> group_carrier(subgroup_generated G
           (h INTER group_setmul G t (group_setmul G s (group_setinv G t)))) =
          h`;;

(* ------------------------------------------------------------------------- *)
(* Normal subgroups.                                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("normal_subgroup_of",(12,"right"));;

let normal_subgroup_of = new_definition
  `(n:A->bool) normal_subgroup_of (G:A group) <=>
        n subgroup_of G /\
        !x. x IN group_carrier G ==> left_coset G x n = right_coset G n x`;;

let NORMAL_SUBGROUP_IMP_SUBGROUP = `!G n:A->bool. n normal_subgroup_of G ==> n subgroup_of G`;;

let NORMAL_SUBGROUP_OF_IMP_SUBSET = `!G n:A->bool. n normal_subgroup_of G ==> n SUBSET group_carrier G`;;

let NORMAL_SUBGROUP_OF_OPPOSITE_GROUP = `!G n:A->bool.
        n normal_subgroup_of opposite_group G <=> n normal_subgroup_of G`;;

let ABELIAN_GROUP_NORMAL_SUBGROUP = `!G n:A->bool.
        abelian_group G ==> (n normal_subgroup_of G <=> n subgroup_of G)`;;

let NORMAL_SUBGROUP_CONJUGATE_ALT = `!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\
        !x. x IN group_carrier G
            ==> group_setmul G {group_inv G x} (group_setmul G n {x}) = n`;;

let NORMAL_SUBGROUP_CONJUGATE_INV = `!G n:A->bool.
      n normal_subgroup_of G <=>
      n subgroup_of G /\
      !x. x IN group_carrier G
          ==> group_setmul G {group_inv G x} (group_setmul G n {x}) SUBSET n`;;

let NORMAL_SUBGROUP_CONJUGATION_EQ = `!G h:A->bool.
        h normal_subgroup_of G <=>
        h subgroup_of G /\
        !a. a IN group_carrier G ==> IMAGE (group_conjugation G a) h = h`;;

let NORMAL_SUBGROUP_CONJUGATION = `!G h:A->bool.
        h normal_subgroup_of G <=>
        h subgroup_of G /\
        !a. a IN group_carrier G ==> IMAGE (group_conjugation G a) h SUBSET h`;;

let NORMAL_SUBGROUP_CONJUGATION_SUPERSET = `!G h:A->bool.
        h normal_subgroup_of G <=>
        h subgroup_of G /\
        !a. a IN group_carrier G ==> h SUBSET IMAGE (group_conjugation G a) h`;;

let ABELIAN_GROUP_CONJUGATION = `!G a x:A.
        abelian_group G /\ a IN group_carrier G /\ x IN group_carrier G
        ==> group_conjugation G a x = x`;;

let NORMAL_SUBGROUP_OF_INTERS = `!G gs. (!g. g IN gs ==> g normal_subgroup_of G) /\ ~(gs = {})
          ==> INTERS gs normal_subgroup_of G`;;

let NORMAL_SUBGROUP_OF_INTER = `!G g h:A->bool.
        g normal_subgroup_of G /\ h normal_subgroup_of G
        ==> g INTER h normal_subgroup_of G`;;

let NORMAL_SUBGROUP_OF_UNIONS = `!G (u:(A->bool)->bool).
        ~(u = {}) /\
        (!h. h IN u ==> h normal_subgroup_of G) /\
        (!g h. g IN u /\ h IN u ==> g SUBSET h \/ h SUBSET g)
        ==> (UNIONS u) normal_subgroup_of G`;;

let NORMAL_SUBGROUP_ACTION_KERNEL = `!G s (a:A->X->X).
        group_action G s a
        ==> {g | g IN group_carrier G /\ !x. x IN s ==> a g x = x}
            normal_subgroup_of G`;;

let NORMAL_SUBGROUP_LEFT_EQ_RIGHT_COSETS = `!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\
        {left_coset G x n |x| x IN group_carrier G} =
        {right_coset G n x |x| x IN group_carrier G}`;;

let NORMAL_SUBGROUP_LEFT_SUBSET_RIGHT_COSETS,
    NORMAL_SUBGROUP_RIGHT_SUBSET_LEFT_COSETS = (CONJ_PAIR o prove)
 (`(!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\
        {left_coset G x n |x| x IN group_carrier G} SUBSET
        {right_coset G n x |x| x IN group_carrier G}) /\
   (!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\
        {right_coset G n x |x| x IN group_carrier G} SUBSET
        {left_coset G x n |x| x IN group_carrier G})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORMAL_SUBGROUP_LEFT_EQ_RIGHT_COSETS] THEN
  ASM_CASES_TAC `(n:A->bool) subgroup_of G` THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ_ALT] DIFF_UNIONS_PAIRWISE_DISJOINT)) THEN
  ASM_SIMP_TAC[UNIONS_LEFT_COSETS; UNIONS_RIGHT_COSETS; DIFF_EQ_EMPTY;
    PAIRWISE_DISJOINT_RIGHT_COSETS; PAIRWISE_DISJOINT_LEFT_COSETS] THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[EMPTY_UNIONS] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN t ==> ~(P x))
    ==> (!x. x IN t DIFF s ==> P x) ==> t SUBSET s`) THEN
  ASM_SIMP_TAC[FORALL_IN_GSPEC; LEFT_COSET_NONEMPTY; RIGHT_COSET_NONEMPTY]);;

let NORMAL_SUBGROUP_MUL_SYM = `!G h:A->bool.
        h normal_subgroup_of G <=>
        h subgroup_of G /\
        !x y. x IN group_carrier G /\ y IN group_carrier G
              ==> (group_mul G x y IN h <=> group_mul G y x IN h)`;;

let TRIVIAL_NORMAL_SUBGROUP_OF = `!G:A group. {group_id G} normal_subgroup_of G`;;

let CARRIER_NORMAL_SUBGROUP_OF = `!G:A group. (group_carrier G) normal_subgroup_of G`;;

let GROUP_SETINV_RIGHT_COSET = `!G n a:A.
        n normal_subgroup_of G /\ a IN group_carrier G
        ==> group_setinv G (right_coset G n a) =
            right_coset G n (group_inv G a)`;;

let GROUP_SETINV_LEFT_COSET = `!G n a:A.
        n normal_subgroup_of G /\ a IN group_carrier G
        ==> group_setinv G (left_coset G a n) =
            left_coset G (group_inv G a) n`;;

let GROUP_SETMUL_RIGHT_COSET = `!G n a b:A.
        n normal_subgroup_of G /\ a IN group_carrier G /\ b IN group_carrier G
        ==> group_setmul G (right_coset G n a) (right_coset G n b) =
            right_coset G n (group_mul G a b)`;;

let GROUP_SETMUL_LEFT_COSET = `!G n a b:A.
        n normal_subgroup_of G /\ a IN group_carrier G /\ b IN group_carrier G
        ==> group_setmul G (left_coset G a n) (left_coset G b n) =
            left_coset G (group_mul G a b) n`;;

let CROSS_NORMAL_SUBGROUP_OF_PROD_GROUP = `!(G1:A group) (G2:B group) h1 h2.
        (h1 CROSS h2) normal_subgroup_of (prod_group G1 G2) <=>
        h1 normal_subgroup_of G1 /\ h2 normal_subgroup_of G2`;;

let NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED_GEN = `!G s h:A->bool.
        h normal_subgroup_of G /\
        h SUBSET group_carrier(subgroup_generated G s)
        ==> h normal_subgroup_of (subgroup_generated G s)`;;

let NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED = `!G s h:A->bool.
        h normal_subgroup_of G /\ h SUBSET s
        ==> h normal_subgroup_of (subgroup_generated G s)`;;

let GROUP_SETMUL_NORMAL_SUBGROUP_LEFT = `!G n h:A->bool.
        n normal_subgroup_of G /\ h subgroup_of G
        ==> group_setmul G n h subgroup_of G`;;

let GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT = `!G h n:A->bool.
        h subgroup_of G /\ n normal_subgroup_of G
        ==> group_setmul G h n subgroup_of G`;;

let GROUP_SETMUL_NORMAL_SUBGROUP = `!G h k:A->bool.
        h normal_subgroup_of G /\ k normal_subgroup_of G
        ==> group_setmul G h k normal_subgroup_of G`;;

let CARRIER_SUBGROUP_GENERATED_UNION_LEFT = `!G g h:A->bool.
        g normal_subgroup_of G /\ h subgroup_of G
        ==> group_carrier(subgroup_generated G (g UNION h)) =
            group_setmul G g h`;;

let CARRIER_SUBGROUP_GENERATED_UNION_RIGHT = `!G g h:A->bool.
        g subgroup_of G /\ h normal_subgroup_of G
        ==> group_carrier(subgroup_generated G (g UNION h)) =
            group_setmul G g h`;;

(* ------------------------------------------------------------------------- *)
(* Congugate subgroups, or more generally subsets.                           *)
(* ------------------------------------------------------------------------- *)

let group_conjugate = new_definition
 `group_conjugate (G:A group) s t <=>
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G /\
        ?a. a IN group_carrier G /\ IMAGE (group_conjugation G a) s = t`;;

let GROUP_CONJUGATE_REFL = `!G s:A->bool.
        group_conjugate G s s <=> s SUBSET group_carrier G`;;

let GROUP_CONJUGATE_SYM = `!G s t:A->bool. group_conjugate G s t <=> group_conjugate G t s`;;

let GROUP_CONJUGATE_TRANS = `!G s t u:A->bool.
        group_conjugate G s t /\ group_conjugate G t u
        ==> group_conjugate G s u`;;

let GROUP_CONJUGATE_SUBGROUPS_GENERATED = `!G s t:A->bool.
        group_conjugate G s t
        ==> group_conjugate G (group_carrier(subgroup_generated G s))
                              (group_carrier(subgroup_generated G t))`;;

let GROUP_CONJUGATE_IMP_ISOMORPHIC = `!G s t:A->bool.
      group_conjugate G s t
      ==> (subgroup_generated G s) isomorphic_group (subgroup_generated G t)`;;

let GROUP_CONJUGATE_IMP_CARD_EQ = `!G s t:A->bool. group_conjugate G s t ==> s =_c t`;;

let GROUP_ORBIT_CONJUGATE_STABILIZERS = `!G s (a:A->X->X) x y.
      group_action G s a /\ group_orbit G s a x y
      ==> group_conjugate G (group_stabilizer G a x) (group_stabilizer G a y)`;;

let CARD_EQ_GROUP_ORBIT_STABILIZERS = `!G s (a:A->X->X) x y.
        group_action G s a /\ group_orbit G s a x y
        ==> group_stabilizer G a x =_c group_stabilizer G a y`;;

(* ------------------------------------------------------------------------- *)
(* Centralizer and normalizer.                                               *)
(* ------------------------------------------------------------------------- *)

let group_centralizer = new_definition
 `group_centralizer G s =
        {x:A | x IN group_carrier G /\
               !y. y IN group_carrier G /\ y IN s
                   ==> group_mul G x y = group_mul G y x}`;;

let group_normalizer = new_definition
 `group_normalizer G s =
        {x:A | x IN group_carrier G /\
               group_setmul G {x} (group_carrier G INTER s) =
               group_setmul G (group_carrier G INTER s) {x}}`;;

let GROUP_CENTRALIZER = `!G s:A->bool.
        s SUBSET group_carrier G
        ==> group_centralizer G s =
             {x | x IN group_carrier G /\
                  !y. y IN s ==> group_mul G x y = group_mul G y x}`;;

let GROUP_NORMALIZER = `!G s:A->bool.
        s SUBSET group_carrier G
        ==> group_normalizer G s =
             {x | x IN group_carrier G /\
                  group_setmul G {x} s = group_setmul G s {x}}`;;

let GROUP_NORMALIZER_CONJUGATION_EQ = `!G s:A->bool.
        group_normalizer G s =
             {x | x IN group_carrier G /\
                  IMAGE (group_conjugation G x) (group_carrier G INTER s) =
                  (group_carrier G INTER s)}`;;

let GROUP_NORMALIZER_CONJUGATION = `!G s:A->bool.
        s SUBSET group_carrier G
        ==> group_normalizer G s =
            {x | x IN group_carrier G /\ IMAGE (group_conjugation G x) s = s}`;;

let GROUP_NORMALIZER_FINITE = `!G s:A->bool.
        s SUBSET group_carrier G /\ FINITE s
        ==> group_normalizer G s =
            {x | x IN group_carrier G /\
                 IMAGE (group_conjugation G x) s SUBSET s}`;;

let GROUP_CENTRALIZER_RESTRICT = `!G s:A->bool.
        group_centralizer G s =
        group_centralizer G (group_carrier G INTER s)`;;

let GROUP_NORMALIZER_RESTRICT = `!G s:A->bool.
        group_normalizer G s =
        group_normalizer G (group_carrier G INTER s)`;;

let GROUP_CENTRALIZER_SUBSET_CARRIER = `!G s:A->bool. group_centralizer G s SUBSET group_carrier G`;;

let GROUP_NORMALIZER_SUBSET_CARRIER = `!G s:A->bool. group_normalizer G s SUBSET group_carrier G`;;

let FINITE_GROUP_CENTRALIZER = `!(G:A group) s. FINITE(group_carrier G) ==> FINITE(group_centralizer G s)`;;

let FINITE_GROUP_NORMALIZER = `!(G:A group) s. FINITE(group_carrier G) ==> FINITE(group_normalizer G s)`;;

let GROUP_CENTRALIZER_SUBSET_NORMALIZER = `!G s:A->bool. group_centralizer G s SUBSET group_normalizer G s`;;

let SUBGROUP_GROUP_CENTRALIZER = `!G s:A->bool. (group_centralizer G s) subgroup_of G`;;

let SUBGROUP_GROUP_NORMALIZER = `!G s:A->bool. (group_normalizer G s) subgroup_of G`;;

let GROUP_CENTRALIZER_SUBGROUP_GENERATED = `!G h s:A->bool.
        s SUBSET h /\ h subgroup_of G
        ==> group_centralizer (subgroup_generated G h) s =
             h INTER group_centralizer G s`;;

let GROUP_NORMALIZER_SUBGROUP_GENERATED = `!G h s:A->bool.
        s SUBSET h /\ h subgroup_of G
        ==> group_normalizer (subgroup_generated G h) s =
             h INTER group_normalizer G s`;;

let IN_GROUP_CENTRALIZER_ID = `!(G:A group) s. group_id G IN group_centralizer G s`;;

let IN_GROUP_NORMALIZER_ID = `!(G:A group) s. group_id G IN group_normalizer G s`;;

let GROUP_CENTRALIZER_NONEMPTY = `!(G:A group) s. ~(group_centralizer G s = {})`;;

let GROUP_NORMALIZER_NONEMPTY = `!(G:A group) s. ~(group_normalizer G s = {})`;;

let GROUP_CENTRALIZER_SUBSET = `!G s:A->bool.
        s SUBSET group_centralizer G s <=>
        s SUBSET group_carrier G /\
        !a b. a IN s /\ b IN s ==> group_mul G a b = group_mul G b a`;;

let GROUP_CENTRALIZER_SUBSET_EQ = `!G h:A->bool.
        h subgroup_of G
        ==> (h SUBSET group_centralizer G h <=>
             abelian_group(subgroup_generated G h))`;;

let GROUP_CENTRE_EQ_CARRIER = `!G:A group.
        group_centralizer G (group_carrier G) = group_carrier G <=>
        abelian_group G`;;

let GROUP_CENTRALIZER_CENTRALIZER_SUBSET = `!G s:A->bool.
        s SUBSET group_centralizer G (group_centralizer G s) <=>
        s SUBSET group_carrier G`;;

let GROUP_NORMALIZER_MAXIMAL_GEN = `!G h n:A->bool.
        h normal_subgroup_of (subgroup_generated G n) <=>
        h subgroup_of (subgroup_generated G n) /\
        group_carrier G INTER n SUBSET group_normalizer G h`;;

let GROUP_NORMALIZER_MAXIMAL = `!G h n:A->bool.
        n subgroup_of G
        ==> (h normal_subgroup_of (subgroup_generated G n) <=>
             h subgroup_of G /\ h SUBSET n /\ n SUBSET group_normalizer G h)`;;

let NORMAL_SUBGROUP_NORMALIZER_CONTAINS_CARRIER = `!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\ group_carrier G SUBSET group_normalizer G n`;;

let NORMAL_SUBGROUP_NORMALIZER_EQ_CARRIER = `!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\ group_normalizer G n = group_carrier G`;;

let GROUP_NORMALIZER_SUBSET = `!G h:A->bool.
        h subgroup_of G ==> h SUBSET group_normalizer G h`;;

let NORMAL_SUBGROUP_OF_NORMALIZER = `!G h:A->bool.
        h normal_subgroup_of (subgroup_generated G (group_normalizer G h)) <=>
        h subgroup_of G`;;

let GROUP_CENTRALIZER_POINTWISE = `!G s:A->bool.
        group_centralizer G s =
        if s = {} then group_carrier G
        else INTERS {group_centralizer G {x} | x IN s}`;;

let GROUP_CENTRALIZER_ALT = `!G s:A->bool.
        group_centralizer G s =
         {x | x IN group_carrier G /\
              !y. y IN group_carrier G /\ y IN s
                  ==> group_conjugation G x y = y}`;;

let NORMAL_SUBGROUP_CENTRALIZER_NORMALIZER = `!G h:A->bool.
        group_centralizer G h normal_subgroup_of
        subgroup_generated G (group_normalizer G h)`;;

let NORMAL_SUBGROUP_CENTRALIZER = `!G n:A->bool.
        n normal_subgroup_of G
        ==> group_centralizer G n normal_subgroup_of G`;;

let GROUP_NORMALIZER_SING = `!G a:A. group_normalizer G {a} = group_centralizer G {a}`;;

let GROUP_CENTRALIZER_GALOIS_EQ = `!G s t:A->bool.
        s SUBSET group_carrier G /\ t SUBSET group_carrier G
        ==> (s SUBSET group_centralizer G t <=>
             t SUBSET group_centralizer G s)`;;

let GROUP_CENTRALIZER_GALOIS = `!G s t:A->bool.
        s SUBSET group_carrier G /\ t SUBSET group_centralizer G s
        ==> s SUBSET group_centralizer G t`;;

let GROUP_CENTRALIZER_MONO = `!G s t:A->bool.
        s SUBSET t ==> group_centralizer G t SUBSET group_centralizer G s`;;

let GROUP_ACTION_CONJUGATION_NORMAL_SUBGROUP = `!G n:A->bool.
        n normal_subgroup_of G
        ==> group_action G n (group_conjugation G)`;;

let GROUP_STABILIZER_CONJUGATION = `!G a:A.
     a IN group_carrier G
     ==> group_stabilizer G (group_conjugation G) a =
         group_centralizer G {a}`;;

let GROUP_ORBIT_CONJUGATION_GEN = `!G s x:A.
        s SUBSET group_carrier G
        ==> group_orbit G s (group_conjugation G) x =
            if x IN s then {y | y IN s /\ group_conjugate G {x} {y}} else {}`;;

let GROUP_ORBIT_CONJUGATION = `!G x:A.
        group_orbit G (group_carrier G) (group_conjugation G) x =
        if x IN group_carrier G
        then {y | y IN group_carrier G /\ group_conjugate G {x} {y}}
        else {}`;;

let GROUP_ACTION_IMAGE_CONJUGATION = `!G u:(A->bool)->bool.
        (!t. t IN u ==> t SUBSET group_carrier G) /\
        (!g t. g IN group_carrier G /\ t IN u
               ==> IMAGE (group_conjugation G g) t IN u)
        ==> group_action G u (IMAGE o group_conjugation G)`;;

let GROUP_STABILIZER_IMAGE_CONJUGATION = `!G s:A->bool.
        s SUBSET group_carrier G
        ==> group_stabilizer G (IMAGE o group_conjugation G) s =
            group_normalizer G s`;;

let GROUP_ACTION_IMAGE_CONJUGATION_CARRIER = `!G:A group. group_action G {s | s SUBSET group_carrier G}
                              (IMAGE o group_conjugation G)`;;

let GROUP_ACTION_IMAGE_CONJUGATION_SUBGROUPS = `!G:A group. group_action G {n | n subgroup_of G}
                              (IMAGE o group_conjugation G)`;;

let GROUP_ORBIT_IMAGE_CONJUGATION = `!G. group_orbit G {s | s SUBSET group_carrier G}
                     (IMAGE o group_conjugation G) =
       group_conjugate G`;;

let GROUP_ORBIT_IMAGE_CONJUGATION_GEN = `!G u s:A->bool.
        (!t. t IN u ==> t SUBSET group_carrier G) /\ s IN u
        ==> group_orbit G u (IMAGE o group_conjugation G) s =
            \t. t IN u /\ group_conjugate G s t`;;

let CARD_CONJUGATE_SUBSETS_MUL_GEN = `!G s:A->bool.
        s SUBSET group_carrier G
        ==> {t | group_conjugate G s t} *_c group_normalizer G s =_c
            group_carrier G`;;

let CARD_CONJUGATE_SUBSETS_MUL = `!G s:A->bool.
        FINITE(group_carrier G) /\ s SUBSET group_carrier G
        ==> CARD {t | group_conjugate G s t} * CARD(group_normalizer G s) =
            CARD(group_carrier G)`;;

let CARD_CONJUGATE_SUBSETS = `!G s:A->bool.
        FINITE(group_carrier G) /\ s SUBSET group_carrier G
        ==> CARD {t | group_conjugate G s t} =
            CARD(group_carrier G) DIV CARD(group_normalizer G s)`;;

(* ------------------------------------------------------------------------- *)
(* Quotient groups.                                                          *)
(* ------------------------------------------------------------------------- *)

let quotient_group = new_definition
 `quotient_group G (n:A->bool) =
        group ({right_coset G n x |x| x IN group_carrier G},
               n,group_setinv G,group_setmul G)`;;

let QUOTIENT_GROUP = `(!G n:A->bool.
        n normal_subgroup_of G
        ==> group_carrier(quotient_group G n) =
              {right_coset G n x |x| x IN group_carrier G}) /\
   (!G n:A->bool.
        n normal_subgroup_of G
        ==> group_id(quotient_group G n) = n) /\
   (!G n:A->bool.
        n normal_subgroup_of G
        ==> group_inv(quotient_group G n) = group_setinv G) /\
   (!G n:A->bool.
        n normal_subgroup_of G
        ==> group_mul(quotient_group G n) = group_setmul G)`;;

let ABELIAN_QUOTIENT_GROUP = `!G n:A->bool.
     abelian_group G /\ n subgroup_of G ==> abelian_group(quotient_group G n)`;;

let FINITE_QUOTIENT_GROUP = `!G n:A->bool.
        FINITE(group_carrier G) /\ n normal_subgroup_of G
        ==> FINITE(group_carrier(quotient_group G n))`;;

let TRIVIAL_QUOTIENT_GROUP = `!G n:A->bool.
        trivial_group G /\  n normal_subgroup_of G
        ==> trivial_group(quotient_group G n)`;;

let QUOTIENT_GROUP_ID = `!G n:A->bool.
        n normal_subgroup_of G
        ==> group_id(quotient_group G n) = n`;;

let QUOTIENT_GROUP_INV = `!G n a:A.
        n normal_subgroup_of G /\ a IN group_carrier G
        ==> group_inv (quotient_group G n) (right_coset G n a) =
            right_coset G n (group_inv G a)`;;

let QUOTIENT_GROUP_MUL = `!G n a b:A.
        n normal_subgroup_of G /\ a IN group_carrier G /\ b IN group_carrier G
        ==> group_mul (quotient_group G n)
                      (right_coset G n a) (right_coset G n b) =
            right_coset G n (group_mul G a b)`;;

let QUOTIENT_GROUP_DIV = `!G n a b:A.
        n normal_subgroup_of G /\ a IN group_carrier G /\ b IN group_carrier G
        ==> group_div (quotient_group G n)
                      (right_coset G n a) (right_coset G n b) =
            right_coset G n (group_div G a b)`;;

let QUOTIENT_GROUP_POW = `!G n (a:A) k.
        n normal_subgroup_of G /\ a IN group_carrier G
        ==> group_pow (quotient_group G n) (right_coset G n a) k =
            right_coset G n (group_pow G a k)`;;

let QUOTIENT_GROUP_ZPOW = `!G n (a:A) k.
        n normal_subgroup_of G /\ a IN group_carrier G
        ==> group_zpow (quotient_group G n) (right_coset G n a) k =
            right_coset G n (group_zpow G a k)`;;

let GROUP_HOMOMORPHISM_RIGHT_COSET = `!G n:A->bool.
        n normal_subgroup_of G
        ==> group_homomorphism (G,quotient_group G n) (right_coset G n)`;;

let GROUP_EPIMORPHISM_RIGHT_COSET = `!G n:A->bool.
        n normal_subgroup_of G
        ==> group_epimorphism (G,quotient_group G n) (right_coset G n)`;;

let CARD_LE_QUOTIENT_GROUP = `!G n:A->bool.
        n normal_subgroup_of G
        ==> group_carrier(quotient_group G n) <=_c group_carrier G`;;

let CARD_QUOTIENT_GROUP_DIVIDES = `!G n:A->bool.
        FINITE(group_carrier G) /\ n normal_subgroup_of G
        ==> CARD(group_carrier(quotient_group G n)) divides
            CARD(group_carrier G)`;;

let TRIVIAL_QUOTIENT_GROUP_EQ = `!G n:A->bool.
        n normal_subgroup_of G
        ==> (trivial_group(quotient_group G n) <=> n = group_carrier G)`;;

let TRIVIAL_QUOTIENT_GROUP_SELF = `!G:A group. trivial_group(quotient_group G (group_carrier G))`;;

let QUOTIENT_GROUP_TRIVIAL = `!G:A group. quotient_group G {group_id G} isomorphic_group G`;;

let GROUP_ISOMORPHISM_PROD_QUOTIENT_GROUP = `!(G1:A group) (G2:B group) n1 n2.
        n1 normal_subgroup_of G1 /\ n2 normal_subgroup_of G2
        ==> group_isomorphism(prod_group (quotient_group G1 n1)
                                         (quotient_group G2 n2),
                              quotient_group (prod_group G1 G2) (n1 CROSS n2))
                             (\(s,t). s CROSS t)`;;

let ISOMORPHIC_QUOTIENT_PROD_GROUP = `!(G1:A group) (G2:B group) n1 n2.
        n1 normal_subgroup_of G1 /\ n2 normal_subgroup_of G2
        ==> quotient_group (prod_group G1 G2) (n1 CROSS n2) isomorphic_group
            prod_group (quotient_group G1 n1) (quotient_group G2 n2)`;;

let CARTESIAN_PRODUCT_NORMAL_SUBGROUP_OF_PRODUCT_GROUP = `!(G:K->A group) h k.
        (cartesian_product k h) normal_subgroup_of (product_group k G) <=>
        !i. i IN k ==> (h i) normal_subgroup_of (G i)`;;

let GROUP_ISOMORPHISM_PRODUCT_QUOTIENT_GROUP = `!(G:K->A group) n k.
        (!i. i IN k ==> (n i) normal_subgroup_of (G i))
        ==> group_isomorphism
              (product_group k (\i. quotient_group (G i) (n i)),
               quotient_group (product_group k G) (cartesian_product k n))
              (cartesian_product k)`;;

let ISOMORPHIC_QUOTIENT_PRODUCT_GROUP = `!(G:K->A group) n k.
        (!i. i IN k ==> (n i) normal_subgroup_of (G i))
        ==> (quotient_group (product_group k G) (cartesian_product k n))
            isomorphic_group
            (product_group k (\i. quotient_group (G i) (n i)))`;;

let SUBGROUP_OF_QUOTIENT_GROUP,SUBGROUP_OF_QUOTIENT_GROUP_ALT =
 (CONJ_PAIR o prove)
 (`(!G n h:(A->bool)->bool.
        n normal_subgroup_of G
        ==> (h subgroup_of quotient_group G n <=>
             ?k. k subgroup_of G /\ { right_coset G n x | x IN k} = h)) /\
   (!G n h:(A->bool)->bool.
        n normal_subgroup_of G
        ==> (h subgroup_of quotient_group G n <=>
             ?k. k subgroup_of G /\
                 n SUBSET k /\
                 { right_coset G n x | x IN k} = h))`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
    `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(TAUT
   `(r ==> q) /\ (p ==> r) /\ (q ==> p)
    ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    DISCH_TAC THEN
    EXISTS_TAC `{x:A | x IN group_carrier G /\ right_coset G n x IN h}` THEN
    MATCH_MP_TAC(TAUT `q /\ p /\ r ==> p /\ q /\ r`) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP IN_SUBGROUP_ID) THEN
      MATCH_MP_TAC(SET_RULE
       `n SUBSET {x | x IN s /\ f x = z}
        ==> z IN h ==> n SUBSET {x | x IN s /\ f x IN h}`) THEN
      ASM_SIMP_TAC[QUOTIENT_GROUP; SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[RIGHT_COSET_EQ_SUBGROUP; normal_subgroup_of;
                    subgroup_of; SUBSET];
      REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC SUBGROUP_OF_EPIMORPHIC_PREIMAGE THEN
      EXISTS_TAC `quotient_group (G:A group) n` THEN
      ASM_SIMP_TAC[GROUP_EPIMORPHISM_RIGHT_COSET; ETA_AX]];
    DISCH_THEN(X_CHOOSE_THEN `k:A->bool`
     (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC SUBGROUP_OF_HOMOMORPHIC_IMAGE THEN
    EXISTS_TAC `G:A group` THEN
    ASM_SIMP_TAC[GROUP_HOMOMORPHISM_RIGHT_COSET; ETA_AX]]);;

let SUBGROUP_OF_QUOTIENT_GROUP_GENERATED_BY = `!G n h:(A->bool)->bool.
        n normal_subgroup_of G /\ h subgroup_of quotient_group G n
        ==> ?k. k subgroup_of G /\ n SUBSET k /\
                quotient_group (subgroup_generated G k) n =
                subgroup_generated (quotient_group G n) h`;;

let QUOTIENT_GROUP_SUBGROUP_GENERATED = `!G h n:A->bool.
        n normal_subgroup_of G /\ h subgroup_of G /\ n SUBSET h
        ==> quotient_group (subgroup_generated G h) n =
            subgroup_generated (quotient_group G n)
                               {right_coset G n x | x IN h}`;;

(* ------------------------------------------------------------------------- *)
(* Kernels and images of homomorphisms.                                      *)
(* ------------------------------------------------------------------------- *)

let group_kernel = new_definition
 `group_kernel (G,G') (f:A->B) =
    {x | x IN group_carrier G /\ f x = group_id G'}`;;

let group_image = new_definition
 `group_image (G:A group,G':B group) (f:A->B) = IMAGE f (group_carrier G)`;;

let GROUP_KERNEL_ID = `!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> group_id G IN group_kernel (G,G') f`;;

let GROUP_KERNEL_NONEMPTY = `!G H (f:A->B).
        group_homomorphism(G,H) f ==> ~(group_kernel(G,H) f = {})`;;

let GROUP_KERNEL_SUBSET_CARRIER = `!G H (f:A->B). group_kernel(G,H) f SUBSET group_carrier G`;;

let GROUP_MONOMORPHISM = `!G G' (f:A->B).
        group_monomorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_kernel (G,G') f = {group_id G}`;;

let GROUP_MONOMORPHISM_ALT = `!G G' (f:A->B).
        group_monomorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        !x. x IN group_carrier G /\ f x = group_id G' ==> x = group_id G`;;

let GROUP_MONOMORPHISM_ALT_EQ = `!G G' f:A->B.
        group_monomorphism (G,G') f <=>
        group_homomorphism (G,G') f /\
        !x. x IN group_carrier G ==> (f x = group_id G' <=> x = group_id G)`;;

let GROUP_EPIMORPHISM = `!G G' (f:A->B).
        group_epimorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_image (G,G') f = group_carrier G'`;;

let GROUP_EPIMORPHISM_ALT = `!G G' (f:A->B).
        group_epimorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_carrier G' SUBSET group_image (G,G') f`;;

let GROUP_ISOMORPHISM_EPIMORPHISM_ALT = `!G G' (f:A->B).
        group_isomorphism (G,G') f <=>
        group_epimorphism (G,G') f /\
        (!x. x IN group_carrier G /\ f x = group_id G' ==> x = group_id G)`;;

let GROUP_ISOMORPHISM_GROUP_KERNEL_GROUP_IMAGE = `!G G' (f:A->B).
        group_isomorphism (G,G') f <=>
        group_homomorphism(G,G') f /\
        group_kernel (G,G') f = {group_id G} /\
        group_image (G,G') f = group_carrier G'`;;

let GROUP_ISOMORPHISM_ALT = `!G G' (f:A->B).
      group_isomorphism (G,G') f <=>
      IMAGE f (group_carrier G) = group_carrier G' /\
      (!x y. x IN group_carrier G /\ y IN group_carrier G
             ==> f(group_mul G x y) = group_mul G' (f x) (f y)) /\
      (!x. x IN group_carrier G /\ f x = group_id G' ==> x = group_id G)`;;

let SUBGROUP_GROUP_KERNEL = `!G G' (f:A->B).
        group_homomorphism(G,G') f ==> (group_kernel (G,G') f) subgroup_of G`;;

let SUBGROUP_GROUP_IMAGE = `!G G' (f:A->B).
        group_homomorphism(G,G') f ==> (group_image (G,G') f) subgroup_of G'`;;

let GROUP_KERNEL_TO_SUBGROUP_GENERATED = `!G H s (f:A->B).
        group_kernel (G,subgroup_generated H s) f = group_kernel(G,H) f`;;

let GROUP_IMAGE_TO_SUBGROUP_GENERATED = `!G H s (f:A->B).
        group_image (G,subgroup_generated H s) f = group_image(G,H) f`;;

let GROUP_KERNEL_FROM_SUBGROUP_GENERATED = `!G H s f:A->B.
        s subgroup_of G
        ==> group_kernel(subgroup_generated G s,H) f =
            group_kernel(G,H) f INTER s`;;

let GROUP_IMAGE_FROM_SUBGROUP_GENERATED = `!G H s f:A->B.
        s subgroup_of G
        ==> group_image(subgroup_generated G s,H) f =
            group_image(G,H) f INTER IMAGE f s`;;

let GROUP_ISOMORPHISM_ONTO_IMAGE = `!(f:A->B) G H.
        group_isomorphism(G,subgroup_generated H (group_image (G,H) f)) f <=>
        group_monomorphism(G,H) f`;;

let NORMAL_SUBGROUP_GROUP_KERNEL = `!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> (group_kernel (G,G') f) normal_subgroup_of G`;;

let GROUP_KERNEL_RIGHT_COSET = `!G n:A->bool.
        n normal_subgroup_of G
        ==> group_kernel(G,quotient_group G n) (right_coset G n) = n`;;

let CARD_EQ_GROUP_IMAGE_KERNEL = `!G H (f:A->B).
        group_homomorphism(G,H) f
        ==> group_image(G,H) f *_c group_kernel(G,H) f =_c group_carrier G`;;

let CARD_DIVIDES_GROUP_MONOMORPHIC_IMAGE = `!G H (f:A->B).
        group_monomorphism(G,H) f /\ FINITE(group_carrier H)
        ==> CARD(group_carrier G) divides CARD(group_carrier H)`;;

let CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE = `!G H (f:A->B).
        group_epimorphism(G,H) f /\ FINITE(group_carrier G)
        ==> CARD(group_carrier H) divides CARD(group_carrier G)`;;

let QUOTIENT_GROUP_UNIVERSAL_EXPLICIT = `!G G' n (f:A->B).
        group_homomorphism (G,G') f /\ n normal_subgroup_of G /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G /\
               right_coset G n x = right_coset G n y
               ==> f x = f y)
        ==> ?g. group_homomorphism(quotient_group G n,G') g /\
                !x. x IN group_carrier G ==> g(right_coset G n x) = f x`;;

let QUOTIENT_GROUP_UNIVERSAL = `!G G' n (f:A->B).
        group_homomorphism (G,G') f /\
        n normal_subgroup_of G /\
        n SUBSET group_kernel (G,G') f
        ==> ?g. group_homomorphism(quotient_group G n,G') g /\
                !x. x IN group_carrier G ==> g(right_coset G n x) = f x`;;

let QUOTIENT_GROUP_UNIVERSAL_EPIMORPHISM = `!G G' n (f:A->B).
        group_epimorphism (G,G') f /\
        n normal_subgroup_of G /\
        n SUBSET group_kernel (G,G') f
        ==> ?g. group_epimorphism(quotient_group G n,G') g /\
                !x. x IN group_carrier G ==> g(right_coset G n x) = f x`;;

let GROUP_KERNEL_FROM_TRIVIAL_GROUP = `!G H (f:A->B).
        group_homomorphism (G,H) f /\ trivial_group G
        ==> group_kernel (G,H) f = group_carrier G`;;

let GROUP_IMAGE_FROM_TRIVIAL_GROUP = `!G H (f:A->B).
        group_homomorphism (G,H) f /\ trivial_group G
        ==> group_image (G,H) f = {group_id H}`;;

let GROUP_KERNEL_TO_TRIVIAL_GROUP = `!G H (f:A->B).
        group_homomorphism (G,H) f /\ trivial_group H
        ==> group_kernel (G,H) f = group_carrier G`;;

let GROUP_IMAGE_TO_TRIVIAL_GROUP = `!G H (f:A->B).
        group_homomorphism (G,H) f /\ trivial_group H
        ==> group_image (G,H) f = group_carrier H`;;

let FIRST_GROUP_ISOMORPHISM_THEOREM = `!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> (quotient_group G (group_kernel (G,G') f)) isomorphic_group
            (subgroup_generated G' (group_image (G,G') f))`;;

let FIRST_GROUP_EPIMORPHISM_THEOREM = `!G G' (f:A->B).
        group_epimorphism(G,G') f
        ==> (quotient_group G (group_kernel (G,G') f)) isomorphic_group G'`;;

let GROUP_HOMOMORPHISM_PREIMAGE_IMAGE_RIGHT = `!G H (f:A->B) s.
        group_homomorphism(G,H) f /\ s SUBSET group_carrier G
        ==> {x | x IN group_carrier G /\ f x IN IMAGE f s} =
            group_setmul G s (group_kernel(G,H) f)`;;

let GROUP_HOMOMORPHISM_PREIMAGE_IMAGE_LEFT = `!G H (f:A->B) s.
        group_homomorphism(G,H) f /\ s SUBSET group_carrier G
        ==> {x | x IN group_carrier G /\ f x IN IMAGE f s} =
            group_setmul G (group_kernel(G,H) f) s`;;

let GROUP_HOMOMORPHISM_IMAGE_PREIMAGE = `!G H (f:A->B) t.
        group_homomorphism(G,H) f
        ==> IMAGE f {x | x IN group_carrier G /\ f x IN t} =
            t INTER (group_image(G,H) f)`;;

let GROUP_HOMOMORPHISM_PREIMAGE_IMAGE = `!G H (f:A->B) s.
        group_homomorphism(G,H) f /\
        group_kernel(G,H) f SUBSET s /\
        s subgroup_of G
        ==> {x | x IN group_carrier G /\ f x IN IMAGE f s} = s`;;

let GROUP_HOMOMORPHISM_IMAGE_PREIMAGE_EQ = `!G H (f:A->B) t.
        group_homomorphism(G,H) f /\ t SUBSET group_image(G,H) f
        ==> IMAGE f {x | x IN group_carrier G /\ f x IN t} = t`;;

let GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE = `!G H (f:A->B) k.
        group_epimorphism(G,H) f
        ==> (k subgroup_of H <=>
             ?j. j subgroup_of G /\
                 group_kernel(G,H) f SUBSET j /\
                 {x | x IN group_carrier G /\ f x IN k} = j /\
                 IMAGE f j = k)`;;

let GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE_ALT = `!G H (f:A->B) j.
        group_epimorphism(G,H) f
        ==> (j subgroup_of G /\ group_kernel(G,H) f SUBSET j <=>
             ?k. k subgroup_of H /\
                 {x | x IN group_carrier G /\ f x IN k} = j /\
                 IMAGE f j = k)`;;

let NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE = `!G H (f:A->B) j.
        group_homomorphism(G,H) f /\ j normal_subgroup_of H
        ==> {x | x IN group_carrier G /\ f x IN j} normal_subgroup_of G`;;

let NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE = `!G H (f:A->B) n.
        group_epimorphism(G,H) f /\ n normal_subgroup_of G
        ==> IMAGE f n normal_subgroup_of H`;;

let NORMAL_SUBGROUP_OF_EPIMORPHIC_PREIMAGE_EQ = `!G H (f:A->B) j k.
        group_epimorphism (G,H) f /\
        k subgroup_of H /\
        {x | x IN group_carrier G /\ f x IN k} = j
        ==> (j normal_subgroup_of G <=> k normal_subgroup_of H)`;;

let GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE = `!G H (f:A->B) k.
        group_epimorphism(G,H) f
        ==> (k normal_subgroup_of H <=>
             ?j. j normal_subgroup_of G /\
                 group_kernel(G,H) f SUBSET j /\
                 {x | x IN group_carrier G /\ f x IN k} = j /\
                 IMAGE f j = k)`;;

let GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE_ALT = `!G H (f:A->B) j.
        group_epimorphism(G,H) f
        ==> (j normal_subgroup_of G /\ group_kernel(G,H) f SUBSET j <=>
             ?k. k normal_subgroup_of H /\
                 {x | x IN group_carrier G /\ f x IN k} = j /\
                 IMAGE f j = k)`;;

let SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ = `!G H (f:A->B) j.
        group_isomorphism(G,H) f /\ j SUBSET group_carrier G
        ==> ((IMAGE f j) subgroup_of H <=> j subgroup_of G)`;;

let NORMAL_SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ = `!G H (f:A->B) j.
        group_isomorphism(G,H) f /\ j SUBSET group_carrier G
        ==> ((IMAGE f j) normal_subgroup_of H <=> j normal_subgroup_of G)`;;

let GROUP_CONJUGATE_SUBGROUP_OF = `!G s t:A->bool.
        group_conjugate G s t
        ==> (s subgroup_of G <=> t subgroup_of G)`;;

let GROUP_CONJUGATE_NORMAL_SUBGROUP_OF = `!G s t:A->bool.
        group_conjugate G s t
        ==> (s normal_subgroup_of G <=> t normal_subgroup_of G)`;;

let NORMAL_SUBGROUP_CONJUGATE = `!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\ !n'. group_conjugate G n n' ==> n' = n`;;

let NORMAL_SUBGROUP_CONJUGATE_EQ = `!G n n':A->bool.
        n normal_subgroup_of G \/ n' normal_subgroup_of G
        ==> (group_conjugate G n n' <=> n = n')`;;

let QUOTIENT_SUBGROUP_CORRESPONDENCE = `!(G:A group) j k.
        j normal_subgroup_of G
        ==> (k subgroup_of (quotient_group G j) <=>
             ?i. i subgroup_of G /\ j SUBSET i /\
                 {x | x IN group_carrier G /\ right_coset G j x IN k} = i /\
                 IMAGE (right_coset G j) i = k)`;;

let QUOTIENT_NORMAL_SUBGROUP_CORRESPONDENCE = `!(G:A group) j k.
        j normal_subgroup_of G
        ==> (k normal_subgroup_of (quotient_group G j) <=>
             ?i. i normal_subgroup_of G /\ j SUBSET i /\
                 {x | x IN group_carrier G /\ right_coset G j x IN k} = i /\
                 IMAGE (right_coset G j) i = k)`;;

let FIRST_GROUP_ISOMORPHISM_THEOREM_GEN = `!G H (f:A->B) j k.
        group_epimorphism(G,H) f /\
        k normal_subgroup_of H /\ {x | x IN group_carrier G /\ f x IN k} = j
        ==> quotient_group G j isomorphic_group quotient_group H k`;;

let FIRST_GROUP_ISOMORPHISM_THEOREM_GEN_ALT = `!G H (f:A->B) j k.
        group_epimorphism(G,H) f /\ j normal_subgroup_of G /\
        group_kernel (G,H) f SUBSET j /\ IMAGE f j = k
        ==> quotient_group G j isomorphic_group quotient_group H k`;;

let SIMPLE_GROUP_EPIMORPHIC_IMAGE_EQ = `!G H (f:A->B).
      group_epimorphism(G,H) f
      ==> ((!k. k normal_subgroup_of H
                ==> k = {group_id H} \/ k = group_carrier H) <=>
           (!h. h normal_subgroup_of G /\ group_kernel(G,H) f PSUBSET h
                ==> h = group_carrier G))`;;

let NO_PROPER_SUBGROUP_EPIMORPHIC_IMAGE_EQ = `!G H (f:A->B).
      group_epimorphism(G,H) f
      ==> ((!k. k subgroup_of H
                ==> k = {group_id H} \/ k = group_carrier H) <=>
           (!h. h subgroup_of G /\ group_kernel(G,H) f PSUBSET h
                ==> h = group_carrier G))`;;

let MAXIMAL_SUBGROUP = `!G n:A->bool.
        n normal_subgroup_of G
        ==> ((!h. h subgroup_of G /\ n PSUBSET h ==> h = group_carrier G) <=>
             (!k. k subgroup_of quotient_group G n
                  ==> k = {group_id(quotient_group G n)} \/
                      k = group_carrier(quotient_group G n)))`;;

let MAXIMAL_NORMAL_SUBGROUP = `!G n:A->bool.
        n normal_subgroup_of G
        ==> ((!h. h normal_subgroup_of G /\ n PSUBSET h
                  ==> h = group_carrier G) <=>
             (!k. k normal_subgroup_of quotient_group G n
                  ==> k = {group_id(quotient_group G n)} \/
                      k = group_carrier(quotient_group G n)))`;;

(* ------------------------------------------------------------------------- *)
(* Trivial homomorphisms.                                                    *)
(* ------------------------------------------------------------------------- *)

let trivial_homomorphism = new_definition
 `trivial_homomorphism(G,G') (f:A->B) <=>
        group_homomorphism(G,G') f /\
        !x. x IN group_carrier G ==> f x = group_id G'`;;

let GROUP_KERNEL_IMAGE_TRIVIAL = `!(f:A->B) G G'.
        group_homomorphism (G,G') f
        ==> (group_kernel(G,G') f = group_carrier G <=>
             group_image(G,G') f = {group_id G'})`;;

let TRIVIAL_HOMOMORPHISM_GROUP_KERNEL = `!(f:A->B) G G'.
        trivial_homomorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_kernel(G,G') f = group_carrier G`;;

let TRIVIAL_HOMOMORPHISM_GROUP_IMAGE = `!(f:A->B) G G'.
        trivial_homomorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_image(G,G') f = {group_id G'}`;;

let TRIVIAL_HOMOMORPHISM_TRIVIAL = `!G H. trivial_homomorphism (G,H) (\x. group_id H)`;;

let GROUP_MONOMORPHISM_TRIVIAL = `!G H. group_monomorphism (G,H) (\x. group_id H) <=> trivial_group G`;;

let GROUP_EPIMORPHISM_TRIVIAL = `!G H. group_epimorphism (G,H) (\x. group_id H) <=> trivial_group H`;;

let GROUP_ISOMORPHISM_TRIVIAL = `!G H. group_isomorphism (G,H) (\x. group_id H) <=>
         trivial_group G /\ trivial_group H`;;

(* ------------------------------------------------------------------------- *)
(* The order of a group element. This is defined as 0 for the infinite case. *)
(* This keeps theorems uniform and is analogous to "characteristic zero".    *)
(* That is, x^n = 1 iff n is divisible by the order of x, in all cases.      *)
(* ------------------------------------------------------------------------- *)

let group_element_order = new_definition
 `group_element_order G (x:A) =
        @d. !n. group_pow G x n = group_id G <=> d divides n`;;

let GROUP_POW_EQ_ID = `!G (x:A) n.
        x IN group_carrier G
        ==> (group_pow G x n = group_id G <=>
             (group_element_order G x) divides n)`;;

let GROUP_POW_EQ_ID_DIVISOR = `!G (x:A) m n.
        x IN group_carrier G /\
        group_pow G x m = group_id G /\
        m divides n
        ==> group_pow G x n = group_id G`;;

let GROUP_POW_ELEMENT_ORDER = `!G x:A. x IN group_carrier G
           ==> group_pow G x (group_element_order G x) = group_id G`;;

let GROUP_ZPOW_EQ_ID = `!G (x:A) n.
        x IN group_carrier G
        ==> (group_zpow G x n = group_id G <=>
             &(group_element_order G x) divides n)`;;

let GROUP_ZPOW_EQ_ID_DIVISOR = `!G (x:A) m n.
        x IN group_carrier G /\
        group_zpow G x m = group_id G /\
        m divides n
        ==> group_zpow G x n = group_id G`;;

let GROUP_ZPOW_EQ_ALT = `!G (x:A) m n.
        x IN group_carrier G
        ==> (group_zpow G x m = group_zpow G x n <=>
             &(group_element_order G x) divides n - m)`;;

let GROUP_ZPOW_EQ = `!G (x:A) m n.
        x IN group_carrier G
        ==> (group_zpow G x m = group_zpow G x n <=>
             (m == n) (mod &(group_element_order G x)))`;;

let GROUP_POW_EQ = `!G (x:A) m n.
        x IN group_carrier G
        ==> (group_pow G x m = group_pow G x n <=>
             (m == n) (mod (group_element_order G x)))`;;

let GROUP_ZPOW_REM_ELEMENT_ORDER = `!G (x:A) n.
        x IN group_carrier G
        ==> group_zpow G x (n rem &(group_element_order G x)) =
            group_zpow G x n`;;

let GROUP_POW_MOD_ELEMENT_ORDER = `!G (x:A) n.
        x IN group_carrier G
        ==> group_pow G x (n MOD group_element_order G x) =
            group_pow G x n`;;

let GROUP_ELEMENT_ORDER_EQ_0 = `!G (x:A).
        x IN group_carrier G
        ==> (group_element_order G x = 0 <=>
              !n. ~(n = 0) ==> ~(group_pow G x n = group_id G))`;;

let GROUP_ELEMENT_ORDER_UNIQUE = `!G (x:A) d.
        x IN group_carrier G
        ==> (group_element_order G x = d <=>
             !n. group_pow G x n = group_id G <=> d divides n)`;;

let GROUP_ELEMENT_ORDER_EQ_1 = `!G (x:A).
        x IN group_carrier G
        ==> (group_element_order G x = 1 <=> x = group_id G)`;;

let GROUP_ELEMENT_ORDER_UNIQUE_PRIME = `!G (x:A) p.
        x IN group_carrier G /\ prime p
        ==> (group_element_order G x = p <=>
             ~(x = group_id G) /\ group_pow G x p = group_id G)`;;

let GROUP_ELEMENT_ORDER_ID = `!G:A group. group_element_order G (group_id G) = 1`;;

let GROUP_ELEMENT_ORDER_INV = `!G x:A.
        x IN group_carrier G
        ==> group_element_order G (group_inv G x) = group_element_order G x`;;

let GROUP_POW_GCD_EQ_ID = `!G (x:A) m n.
        x IN group_carrier G
        ==> (group_pow G x (gcd(m,n)) = group_id G <=>
             group_pow G x m = group_id G /\ group_pow G x n = group_id G)`;;

let GROUP_POW_COPRIME_EQ_ID = `!G (x:A) m n.
        x IN group_carrier G /\ coprime(m,n)
        ==> (group_pow G x m = group_id G /\ group_pow G x n = group_id G <=>
             x = group_id G)`;;

let FINITE_GROUP_ELEMENT_ORDER_NONZERO = `!G x:A.
        FINITE(group_carrier G) /\ x IN group_carrier G
        ==> ~(group_element_order G x = 0)`;;

let GROUP_ELEMENT_ORDER_POW = `!G (x:A) k.
        x IN group_carrier G /\ ~(k = 0) /\ k divides group_element_order G x
        ==> group_element_order G (group_pow G x k) =
            group_element_order G x DIV k`;;

let GROUP_ELEMENT_ORDER_POW_GEN = `!G (x:A) k.
        x IN group_carrier G
        ==> group_element_order G (group_pow G x k) =
            if k = 0 then 1
            else group_element_order G x DIV gcd(group_element_order G x,k)`;;

let GROUP_ELEMENT_ORDER_MUL_DIVIDES_GEN = `!G x (y:A) n.
        x IN group_carrier G /\
        y IN group_carrier G /\
        group_mul G x y = group_mul G y x /\
        group_element_order G x divides n /\
        group_element_order G y divides n
        ==> group_element_order G (group_mul G x y) divides n`;;

let ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES_GEN = `!G x (y:A) n.
        abelian_group G /\
        x IN group_carrier G /\
        y IN group_carrier G /\
        group_element_order G x divides n /\
        group_element_order G y divides n
        ==> group_element_order G (group_mul G x y) divides n`;;

let GROUP_ELEMENT_ORDER_MUL_DIVIDES_LCM = `!G x (y:A).
        x IN group_carrier G /\
        y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> group_element_order G (group_mul G x y) divides
            lcm(group_element_order G x,group_element_order G y)`;;

let ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES_LCM = `!G x (y:A).
        abelian_group G /\
        x IN group_carrier G /\
        y IN group_carrier G
        ==> group_element_order G (group_mul G x y) divides
            lcm(group_element_order G x,group_element_order G y)`;;

let GROUP_ELEMENT_ORDER_HOMOMORPHIC_IMAGE = `!G H (f:A->B) x.
        group_homomorphism(G,H) f /\ x IN group_carrier G
        ==> group_element_order H (f x) divides group_element_order G x`;;

let GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE = `!(f:A->B) G H x.
        group_monomorphism(G,H) f /\ x IN group_carrier G
        ==> group_element_order H (f x) = group_element_order G x`;;

let ISOMORPHIC_GROUP_TORSION = `!P (G:A group) (H:B group).
        G isomorphic_group H
        ==> ((!x. x IN group_carrier G ==> P(group_element_order G x)) <=>
             (!y. y IN group_carrier H ==> P(group_element_order H y)))`;;

let GROUP_ELEMENT_ORDER_CONJUGATION = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> group_element_order G (group_conjugation G x y) =
            group_element_order G y`;;

let GROUP_ELEMENT_ORDER_MUL_DIVIDES = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> group_element_order G (group_mul G x y)
            divides (group_element_order G x * group_element_order G y)`;;

let ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES = `!G x y:A.
        abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> group_element_order G (group_mul G x y)
            divides (group_element_order G x * group_element_order G y)`;;

let GROUP_POW_MUL_EQ_ID_SYM = `!G n x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_pow G (group_mul G x y) n = group_id G <=>
             group_pow G (group_mul G y x) n = group_id G)`;;

let GROUP_ELEMENT_ORDER_MUL_SYM = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> group_element_order G (group_mul G x y) =
            group_element_order G (group_mul G y x)`;;

let GROUP_ELEMENT_ORDER_UNIQUE_ALT = `!G (x:A) n.
        x IN group_carrier G /\ ~(n = 0)
        ==> (group_element_order G x = n <=>
             group_pow G x n = group_id G /\
             !m. 0 < m /\ m < n ==> ~(group_pow G x m = group_id G))`;;

let GROUP_ELEMENT_ORDER_EQ_2 = `!G x:A.
        x IN group_carrier G
        ==> (group_element_order G x = 2 <=>
             ~(x = group_id G) /\ group_pow G x 2 = group_id G)`;;

let GROUP_ELEMENT_ORDER_EQ_2_ALT = `!G x:A.
        x IN group_carrier G
        ==> (group_element_order G x = 2 <=>
             ~(x = group_id G) /\ group_inv G x = x)`;;

let GROUP_ELEMENT_ORDER_POW_DIVIDES = `!G (x:A) n.
        x IN group_carrier G
        ==> group_element_order G (group_pow G x n) divides
            group_element_order G x`;;

let GROUP_ELEMENT_ORDER_MUL_EQ = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x /\
        coprime(group_element_order G x,group_element_order G y)
        ==> group_element_order G (group_mul G x y) =
            group_element_order G x * group_element_order G y`;;

let GROUP_ELEMENT_ORDER_EQ_MUL_GEN = `!G (x:A) k n.
        x IN group_carrier G /\ ~(k = 0)
        ==> (group_element_order G x = k * n <=>
             k divides group_element_order G x /\
             group_element_order G (group_pow G x k) = n)`;;

let GROUP_ELEMENT_ORDER_EQ_MUL = `!G (x:A) k n.
        x IN group_carrier G /\ ~(k = 0) /\ k divides n
        ==> (group_element_order G x = k * n <=>
             group_element_order G (group_pow G x k) = n)`;;

let ABELIAN_GROUP_ELEMENT_ORDER_MUL_EQ = `!G x y:A.
        abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G /\
        coprime(group_element_order G x,group_element_order G y)
        ==> group_element_order G (group_mul G x y) =
            group_element_order G x * group_element_order G y`;;

let GROUP_ELEMENT_ORDER_LCM_EXISTS = `!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> ?z. z IN group_carrier G /\
                group_element_order G z =
                lcm(group_element_order G x,group_element_order G y)`;;

let ABELIAN_GROUP_ELEMENT_ORDER_LCM_EXISTS = `!G x y:A.
        abelian_group G /\
        x IN group_carrier G /\ y IN group_carrier G
        ==> ?z. z IN group_carrier G /\
                group_element_order G z =
                lcm(group_element_order G x,group_element_order G y)`;;

let ABELIAN_GROUP_ORDER_DIVIDES_MAXIMAL = `!G:A group.
      abelian_group G /\ FINITE(group_carrier G)
      ==> ?x. x IN group_carrier G /\
              !y. y IN group_carrier G
                  ==> group_element_order G y divides group_element_order G x`;;

let ABELIAN_GROUP_ELEMENT_ORDER_DIVIDES_MAXIMAL_ALT = `!G:A group.
        abelian_group G /\ FINITE(group_carrier G)
        ==> ?x. x IN group_carrier G /\
                !y. y IN group_carrier G
                    ==> group_pow G y (group_element_order G x) = group_id G`;;

let GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED = `!G h x:A.
        group_element_order (subgroup_generated G h) x =
        group_element_order G x`;;

let GROUP_ELEMENT_ORDER_PROD_GROUP = `!(G:A group) (H:B group) x y.
        x IN group_carrier G /\ y IN group_carrier H
        ==> group_element_order (prod_group G H) (x,y) =
            lcm(group_element_order G x,group_element_order H y)`;;

let GROUP_ELEMENT_ORDER_PROD_GROUP_ALT = `!(G:A group) (H:B group) z.
        z IN group_carrier(prod_group G H)
        ==> group_element_order (prod_group G H) z =
            lcm(group_element_order G (FST z),group_element_order H (SND z))`;;

let GROUP_ELEMENT_ORDER_SUM_GROUP = `!(G:K->A group) k x.
        x IN group_carrier(sum_group k G)
        ==> (group_element_order (sum_group k G) x =
             iterate (\m n. lcm(m,n)) k
                     (\i. group_element_order (G i) (x i)))`;;

let GROUP_ELEMENT_ORDER_SUM_GROUP_EQ_0 = `!G k (x:K->A).
        x IN group_carrier (sum_group k G)
        ==> (group_element_order (sum_group k G) x = 0 <=>
             ?i. i IN k /\ group_element_order (G i) (x i) = 0)`;;

let GROUP_ELEMENT_ORDER_COPRIME_DECOMP_EXPLICIT = `!G (x:A) m n.
        coprime(m,n) /\
        x IN group_carrier G /\
        group_element_order G x = m * n
        ==> ?r s. group_element_order G (group_zpow G x r) = m /\
                  group_element_order G (group_zpow G x s) = n /\
                  group_mul G (group_zpow G x r) (group_zpow G x s) = x`;;

let GROUP_ELEMENT_ORDER_COPRIME_DECOMP_UNIQUE = `!G (z:A) m n.
        coprime(m,n) /\
        z IN group_carrier G /\
        group_element_order G z = m * n
        ==> ?!(x,y). x IN group_carrier G /\ y IN group_carrier G /\
                     group_mul G x y = z /\
                     group_mul G y x = z /\
                     group_element_order G x = m /\
                     group_element_order G y = n`;;

let GROUP_ELEMENT_ORDER_COPRIME_DECOMP = `!G (z:A) m n.
        coprime(m,n) /\
        z IN group_carrier G /\
        group_element_order G z = m * n
        ==> ?x y. x IN group_carrier G /\ y IN group_carrier G /\
                  group_mul G x y = z /\
                  group_mul G y x = z /\
                  group_element_order G x = m /\
                  group_element_order G y = n`;;

let GROUP_ELEMENT_ORDER_COPRIME_DECOMP_DIVIDES = `!G (z:A) m n.
        coprime(m,n) /\
        z IN group_carrier G /\
        group_element_order G z divides m * n
        ==> ?x y. x IN group_carrier G /\ y IN group_carrier G /\
                  group_mul G x y = z /\
                  group_mul G y x = z /\
                  group_element_order G x divides m /\
                  group_element_order G y divides n`;;

let GROUP_POW_EQ_ID_DECOMP = `!G (z:A) m n.
        coprime(m,n) /\
        z IN group_carrier G /\
        group_pow G z (m * n) = group_id G
        ==> ?x y. x IN group_carrier G /\ y IN group_carrier G /\
                  group_mul G x y = z /\
                  group_mul G y x = z /\
                  group_pow G x m = group_id G /\
                  group_pow G y n = group_id G`;;

let GROUP_ELEMENT_ORDER_PRIMEPOW_DECOMP = `!G (z:A) p.
        prime p /\
        z IN group_carrier G /\
        ~(group_element_order G z = 0)
        ==> ?x y. x IN group_carrier G /\ y IN group_carrier G /\
                  group_mul G x y = z /\
                  group_mul G y x = z /\
                  (?k. group_element_order G x = p EXP k) /\
                  coprime(p,group_element_order G y)`;;

(* ------------------------------------------------------------------------- *)
(* Torsion subgroups in various generalized forms are indeed subgroups.      *)
(* ------------------------------------------------------------------------- *)

let SUBGROUP_OF_TORSION_GENERAL = `!P G:A group.
        abelian_group G /\
        P 1 /\ (!m n p. p divides lcm(m,n) /\ P m /\ P n ==> P p)
        ==> {x | x IN group_carrier G /\ P(group_element_order G x)}
            subgroup_of G`;;

let SUBGROUP_OF_TORSION_GEN = `!P G:A group.
        abelian_group G /\
        P 1 /\ (!m n p. p divides m * n /\ P m /\ P n ==> P p)
        ==> {x | x IN group_carrier G /\ P(group_element_order G x)}
            subgroup_of G`;;

let SUBGROUP_OF_TORSION = `!G:A group.
        abelian_group G
        ==> {x | x IN group_carrier G /\ ~(group_element_order G x = 0)}
            subgroup_of G`;;

let SUBGROUP_OF_PRIMES_TORSION = `!(G:A group) Q.
        abelian_group G
        ==> {x | x IN group_carrier G /\
                 !p. prime p /\ p divides group_element_order G x
                     ==> Q p}
            subgroup_of G`;;

let SUBGROUP_OF_PRIME_TORSION = `!(G:A group) p.
        abelian_group G /\ prime p
        ==> {x | x IN group_carrier G /\ ?k. group_element_order G x = p EXP k}
            subgroup_of G`;;

let SUBGROUP_OF_LOWER_ORDER = `!(G:A group) n.
        abelian_group G
        ==> {x | x IN group_carrier G /\ group_element_order G x divides n}
            subgroup_of G`;;

let SUBGROUP_OF_LOWER_ORDER_ALT = `!(G:A group) n.
        abelian_group G
        ==> {x | x IN group_carrier G /\ group_pow G x n = group_id G}
            subgroup_of G`;;

let SUBGROUP_OF_NONDIVISIBLE_ORDER = `!(G:A group) p.
        abelian_group G /\ prime p
        ==> {x | x IN group_carrier G /\
                 ~(p divides group_element_order G x)}
            subgroup_of G`;;

let SUBGROUP_OF_COPRIME_ORDER = `!(G:A group) n.
        abelian_group G
        ==> {x | x IN group_carrier G /\
                 coprime(n,group_element_order G x)}
            subgroup_of G`;;

let TORSION_FREE_GROUP = `!G:A group.
        (!x. x IN group_carrier G ==> group_element_order G x <= 1) <=>
        (!x. x IN group_carrier G /\ ~(x = group_id G)
             ==> group_element_order G x = 0)`;;

let TORSION_FREE_GROUP_ALT = `!G:A group.
        (!x. x IN group_carrier G ==> group_element_order G x <= 1) <=>
        (!x n. x IN group_carrier G /\ group_pow G x n = group_id G
               ==> x = group_id G \/ n = 0)`;;

let QUOTIENT_GROUP_POW_EQ_ID = `!(G:A group) n x k.
        n normal_subgroup_of G /\ x IN group_carrier G
        ==> (group_pow (quotient_group G n) (right_coset G n x) k =
             group_id (quotient_group G n) <=>
             group_pow G x k IN n)`;;

let TORSION_FREE_QUOTIENT_GROUP = `!(G:A group) H.
        abelian_group G /\
        quotient_group
          G {x | x IN group_carrier G /\ ~(group_element_order G x = 0)} = H
        ==> !x. x IN group_carrier H ==> group_element_order H x <= 1`;;

let IMAGE_GROUP_CONJUGATION_TORSION_GEN = `!G P a:A.
        a IN group_carrier G
        ==> IMAGE (group_conjugation G a)
                  {x | x IN group_carrier G /\ P(group_element_order G x)} =
            {x | x IN group_carrier G /\ P(group_element_order G x)}`;;

let NORMAL_SUBGROUP_OF_TORSION_GEN = `!P G:A group.
        {x | x IN group_carrier G /\ P(group_element_order G x)}
        normal_subgroup_of G <=>
        {x | x IN group_carrier G /\ P(group_element_order G x)}
        subgroup_of G`;;

let NORMAL_SUBGROUP_OF_TORSION = `!G:A group.
        {x | x IN group_carrier G /\ ~(group_element_order G x = 0)}
        normal_subgroup_of G <=>
        {x | x IN group_carrier G /\ ~(group_element_order G x = 0)}
        subgroup_of G`;;

(* ------------------------------------------------------------------------- *)
(* Cyclic groups.                                                            *)
(* ------------------------------------------------------------------------- *)

let SUBGROUP_OF_POWERS = `!G (x:A).
      x IN group_carrier G ==> {group_zpow G x n | n IN (:int)} subgroup_of G`;;

let CARRIER_SUBGROUP_GENERATED_BY_SING = `!G x:A.
        x IN group_carrier G
        ==> group_carrier(subgroup_generated G {x}) =
            {group_zpow G x n | n IN (:int)}`;;

let cyclic_group = new_definition
 `cyclic_group G <=>
        ?x. x IN group_carrier G /\ subgroup_generated G {x} = G`;;

let CYCLIC_GROUP = `!G:A group.
        cyclic_group G <=>
        ?x. x IN group_carrier G /\
            group_carrier G = {group_zpow G x n | n IN (:int)}`;;

let CYCLIC_IMP_ABELIAN_GROUP = `!G:A group. cyclic_group G ==> abelian_group G`;;

let TRIVIAL_IMP_CYCLIC_GROUP = `!G:A group. trivial_group G ==> cyclic_group G`;;

let CYCLIC_GROUP_ALT = `!G:A group. cyclic_group G <=> ?x. subgroup_generated G {x} = G`;;

let CYCLIC_GROUP_GENERATED = `!G x:A. cyclic_group(subgroup_generated G {x})`;;

let CYCLIC_GROUP_EPIMORPHIC_IMAGE = `!G H (f:A->B).
        group_epimorphism(G,H) f /\ cyclic_group G ==> cyclic_group H`;;

let ISOMORPHIC_GROUP_CYCLICITY = `!(G:A group) (H:B group).
        G isomorphic_group H ==> (cyclic_group G <=> cyclic_group H)`;;

let SUBGROUP_OF_CYCLIC_GROUP_EXPLICIT = `!G h x:A.
        x IN group_carrier G /\ h subgroup_of (subgroup_generated G {x})
        ==> ?k. h = {group_zpow G x (&k * n) | n IN (:int)}`;;

let SUBGROUP_OF_CYCLIC_GROUP = `!G h:A->bool.
        cyclic_group G /\ h subgroup_of G
        ==> cyclic_group(subgroup_generated G h)`;;

let CYCLIC_GROUP_QUOTIENT_GROUP = `!G n:A->bool.
     cyclic_group G /\ n subgroup_of G ==> cyclic_group(quotient_group G n)`;;

let NO_PROPER_SUBGROUPS_IMP_CYCLIC = `!G:A group.
        (!h. h subgroup_of G ==> h SUBSET {group_id G} \/ h = group_carrier G)
        ==> cyclic_group G`;;

let [FINITE_CYCLIC_SUBGROUP; INFINITE_CYCLIC_SUBGROUP;
     FINITE_CYCLIC_SUBGROUP_ALT; INFINITE_CYCLIC_SUBGROUP_ALT] =
 (CONJUNCTS o prove)
 (`(!G x:A.
        x IN group_carrier G
        ==> (FINITE(group_carrier(subgroup_generated G {x})) <=>
             ?n. ~(n = 0) /\ group_pow G x n = group_id G)) /\
   (!G x:A.
        x IN group_carrier G
        ==> (INFINITE(group_carrier(subgroup_generated G {x})) <=>
             !m n. group_pow G x m = group_pow G x n ==> m = n)) /\
   (!G x:A.
        x IN group_carrier G
        ==> (FINITE(group_carrier(subgroup_generated G {x})) <=>
             ?n. ~(n = &0) /\ group_zpow G x n = group_id G)) /\
   (!G x:A.
        x IN group_carrier G
        ==> (INFINITE(group_carrier(subgroup_generated G {x})) <=>
             !m n. group_zpow G x m = group_zpow G x n ==> m = n))`,
  REWRITE_TAC[INFINITE; AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(x:A) IN group_carrier G` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT
   `(r ==> ~p) /\ (r' ==> r) /\ (~r' ==> q) /\ (q ==> q') /\ (q' ==> p)
    ==> (p <=> q) /\ (~p <=> r) /\ (p <=> q') /\ (~p <=> r')`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `(:num)` o MATCH_MP INFINITE_IMAGE_INJ) THEN
    ASM_SIMP_TAC[num_INFINITE; CARRIER_SUBGROUP_GENERATED_BY_SING] THEN
    REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC[GSYM GROUP_NPOW] THEN SET_TAC[];
    REWRITE_TAC[GSYM GROUP_NPOW; GSYM INT_OF_NUM_EQ] THEN SET_TAC[];
    REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP] THEN
    MATCH_MP_TAC INT_WLOG_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:int`; `n:int`] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `num_of_int(n - m)` THEN
    ASM_SIMP_TAC[GSYM GROUP_NPOW; INT_OF_NUM_OF_INT; INT_LT_IMP_LE;
                 INT_SUB_LT; GSYM INT_OF_NUM_EQ; INT_SUB_0; GROUP_ZPOW_SUB;
                 GROUP_DIV_REFL; GROUP_ZPOW];
    REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM GROUP_NPOW] THEN MESON_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `?n. ~(n = 0) /\ group_pow G (x:A) n = group_id G`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `n:int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `num_of_int(abs n)` THEN
      REWRITE_TAC[GSYM GROUP_NPOW; GSYM INT_OF_NUM_EQ] THEN
      SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_ABS_ZERO] THEN
      ASM_REWRITE_TAC[INT_ABS] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[GROUP_ZPOW_NEG; GROUP_INV_ID];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (group_pow G (x:A)) (0..n)` THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING; SUBSET] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; IN_IMAGE; IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `a:int` THEN
      MP_TAC(ISPECL [`a:int`; `&n:int`] INT_DIVISION) THEN
      ASM_REWRITE_TAC[INT_OF_NUM_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
      SPEC_TAC(`a rem &n`,`b:int`) THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
      REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS; INT_ABS_NUM;
                  INT_OF_NUM_LT] THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN EXISTS_TAC `m:num` THEN
      ASM_SIMP_TAC[LT_IMP_LE; GROUP_ZPOW_ADD; GROUP_ZPOW_MUL] THEN
      ASM_REWRITE_TAC[GROUP_NPOW; GROUP_ZPOW_ID] THEN
      ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_POW]]]);;

let FINITE_CYCLIC_SUBGROUP_ORDER = `!G x:A.
        x IN group_carrier G
        ==> (FINITE(group_carrier(subgroup_generated G {x})) <=>
             ~(group_element_order G x = 0))`;;

let INFINITE_CYCLIC_SUBGROUP_ORDER = `!G x:A.
        x IN group_carrier G
        ==> (INFINITE (group_carrier(subgroup_generated G {x})) <=>
             group_element_order G x = 0)`;;

let FINITE_CYCLIC_SUBGROUP_EXPLICIT = `!G x:A.
        FINITE(group_carrier(subgroup_generated G {x})) /\ x IN group_carrier G
        ==> group_carrier(subgroup_generated G {x}) =
            {group_pow G x n |n| n < group_element_order G x}`;;

let FINITE_SUBGROUPS_EQ = `!G:A group. FINITE {h | h subgroup_of G} <=> FINITE(group_carrier G)`;;

let CARD_CYCLIC_SUBGROUP_ORDER = `!G x:A.
        FINITE(group_carrier(subgroup_generated G {x})) /\ x IN group_carrier G
        ==> CARD(group_carrier(subgroup_generated G {x})) =
            group_element_order G x`;;

let PRIME_ORDER_IMP_NO_PROPER_SUBGROUPS = `!(G:A group) p.
        (group_carrier G) HAS_SIZE p /\ (p = 1 \/ prime p)
        ==> !h. h subgroup_of G
                ==> h = {group_id G} \/ h = group_carrier G`;;

let PRIME_ORDER_EQ_NO_PROPER_SUBGROUPS,
    NO_PROPER_SUBGROUPS_EQ_CYCLIC_PRIME_ORDER = (CONJ_PAIR o prove)
 (`(!(G:A group).
        FINITE(group_carrier G) /\
        (CARD(group_carrier G) = 1 \/ prime(CARD(group_carrier G))) <=>
        !h. h subgroup_of G ==> h = {group_id G} \/ h = group_carrier G) /\
   (!(G:A group).
        (!h. h subgroup_of G ==> h = {group_id G} \/ h = group_carrier G) <=>
        cyclic_group G /\
        FINITE(group_carrier G) /\
        (CARD(group_carrier G) = 1 \/ prime(CARD(group_carrier G))))`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> n) /\ (n ==> c) /\ (c /\ n ==> p)
    ==> (p <=> n) /\ (n <=> c /\ p)`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC PRIME_ORDER_IMP_NO_PROPER_SUBGROUPS THEN
    REWRITE_TAC[HAS_SIZE] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC NO_PROPER_SUBGROUPS_IMP_CYCLIC THEN
    ASM SET_TAC[];
    STRIP_TAC THEN REWRITE_TAC[ONE_OR_PRIME]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cyclic_group]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:A group`; `x:A`] INFINITE_CYCLIC_SUBGROUP_ALT) THEN
  ASM_REWRITE_TAC[INFINITE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (TAUT `(~p <=> q) ==> ~q ==> p`)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC
     `{group_zpow G (group_zpow G (x:A) (&2)) n | n IN (:int)}`) THEN
    ASM_SIMP_TAC[SUBGROUP_OF_POWERS; GROUP_ZPOW; GSYM GROUP_ZPOW_MUL] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `{f n | n IN (:int)} = {a} ==> f(&1) = a`)) THEN
      DISCH_TAC THEN
      DISCH_THEN(MP_TAC o SPECL [`&2 * &1:int`; `&0:int`]) THEN
      ASM_REWRITE_TAC[GROUP_ZPOW_0] THEN CONV_TAC INT_ARITH;
      REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:int` (STRIP_ASSUME_TAC o GSYM)) THEN
      DISCH_THEN(MP_TAC o SPECL [`&2 * n:int`; `&1:int`]) THEN
      ASM_SIMP_TAC[GROUP_ZPOW_1] THEN MATCH_MP_TAC(INT_ARITH
       `n:int <= &0 \/ &1 <= n ==> ~(&2 * n = &1)`) THEN
      INT_ARITH_TAC];
    DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[CARD_EQ_0;GROUP_CARRIER_NONEMPTY; NUMBER_RULE
   `0 divides n <=> n = 0`] THEN
  DISCH_TAC THEN
  ABBREV_TAC `m = CARD(group_carrier(G:A group)) DIV n` THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_SIMP_TAC[DIV_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_SIMP_TAC[CARD_EQ_0; GROUP_CARRIER_NONEMPTY; NOT_LT];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `group_carrier(subgroup_generated G {group_pow G x m:A})`) THEN
  SUBGOAL_THEN `group_element_order G (group_pow G (x:A) m) = n`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      GROUP_ELEMENT_ORDER_POW o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `CARD(group_carrier G:A->bool) DIV n = m` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
    ASM_SIMP_TAC[GSYM CARD_CYCLIC_SUBGROUP_ORDER] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST1_TAC) THEN
    ASM_SIMP_TAC[DIV_MULT] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[DIV_MULT] THEN DISCH_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(group_carrier (subgroup_generated G {group_pow G x m:A}))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_CYCLIC_SUBGROUP_ORDER; GROUP_POW] THEN
    ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_POW];
    ALL_TAC] THEN
  REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `CARD:(A->bool)->num`) THEN
  ASM_SIMP_TAC[CARD_CYCLIC_SUBGROUP_ORDER; GROUP_POW; CARD_SING]);;

let ABELIAN_SIMPLE_GROUP = `!G:A group.
        abelian_group G
        ==> ((!h. h normal_subgroup_of G
                  ==> h = {group_id G} \/ h = group_carrier G) <=>
             FINITE(group_carrier G) /\
             (CARD (group_carrier G) = 1 \/ prime(CARD(group_carrier G))))`;;

let PRIME_ORDER_IMP_CYCLIC_GROUP = `!G:A group.
        FINITE(group_carrier G) /\
        (CARD(group_carrier G) = 1 \/ prime(CARD(group_carrier G)))
        ==> cyclic_group G`;;

let GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER = `!G x:A.
        x IN group_carrier G /\ FINITE(group_carrier G)
        ==> (group_element_order G x) divides CARD(group_carrier G)`;;

let GROUP_POW_GROUP_ORDER = `!G x:A.
        x IN group_carrier G /\ FINITE(group_carrier G)
        ==> group_pow G x (CARD(group_carrier G)) = group_id G`;;

let GROUP_ZPOW_REM_ORDER = `!G (x:A) n.
        FINITE(group_carrier G) /\ x IN group_carrier G
        ==> group_zpow G x (n rem &(CARD(group_carrier G))) =
            group_zpow G x n`;;

let GROUP_POW_MOD_ORDER = `!G (x:A) n. FINITE(group_carrier G) /\ x IN group_carrier G
           ==> group_pow G x (n MOD CARD(group_carrier G)) =
               group_pow G x n`;;


let SUBGROUP_OF_FINITE_CYCLIC_GROUP = `!G h a:A.
        FINITE(group_carrier G) /\
        a IN group_carrier G /\
        subgroup_generated G {a} = G
        ==> (h subgroup_of G <=>
             ?d. d divides CARD(group_carrier G) /\
                 h = group_carrier(subgroup_generated G {group_pow G a d}))`;;

let COUNT_FINITE_CYCLIC_GROUP_SUBGROUPS = `!(G:A group) d.
        FINITE(group_carrier G) /\ cyclic_group G
        ==> (CARD {h | h subgroup_of G /\ CARD h = d} =
             if d divides CARD(group_carrier G) then 1 else 0)`;;

let COUNT_FINITE_CYCLIC_GROUP_SUBGROUPS_ALL = `!G:A group.
      FINITE(group_carrier G) /\ cyclic_group G
      ==> CARD {h | h subgroup_of G} =
          CARD {d | d divides CARD(group_carrier G)}`;;

let MAXIMAL_SUBGROUP_PRIME_INDEX = `!G n:A->bool.
        n normal_subgroup_of G
        ==> ((!h. h subgroup_of G /\ n PSUBSET h ==> h = group_carrier G) <=>
             FINITE {right_coset G n x | x | x IN group_carrier G} /\
             (CARD {right_coset G n x | x | x IN group_carrier G} = 1 \/
              prime(CARD {right_coset G n x | x | x IN group_carrier G})))`;;

let PRIME_INDEX_MAXIMAL_PROPER_SUBGROUP = `!G n:A->bool.
        n normal_subgroup_of G
        ==> (FINITE {right_coset G n x | x | x IN group_carrier G} /\
             prime(CARD {right_coset G n x | x | x IN group_carrier G}) <=>
             ~(n = group_carrier G) /\
             !h. h subgroup_of G /\ n PSUBSET h ==> h = group_carrier G)`;;

let MAXIMAL_PROPER_SUBGROUP_PRIME_INDEX = `!G n:A->bool.
        n normal_subgroup_of G /\ ~(n = group_carrier G)
        ==> ((!h. h subgroup_of G /\ n PSUBSET h ==> h = group_carrier G) <=>
             FINITE {right_coset G n x | x | x IN group_carrier G} /\
             prime(CARD {right_coset G n x | x | x IN group_carrier G}))`;;

let GROUP_ZPOW_CANCEL = `!G n x y:A.
        FINITE(group_carrier G) /\ coprime(n,&(CARD(group_carrier G))) /\
        x IN group_carrier G /\ y IN group_carrier G /\
        group_zpow G x n = group_zpow G y n
        ==> x = y`;;

let GROUP_POW_CANCEL = `!G n x y:A.
        FINITE(group_carrier G) /\ coprime(n,CARD(group_carrier G)) /\
        x IN group_carrier G /\ y IN group_carrier G /\
        group_pow G x n = group_pow G y n
        ==> x = y`;;

(* ------------------------------------------------------------------------- *)
(* Finitely generated groups.                                                *)
(* ------------------------------------------------------------------------- *)

let finitely_generated_group = new_definition
 `finitely_generated_group (G:A group) <=>
        ?s. FINITE s /\ subgroup_generated G s = G`;;

let FINITELY_GENERATED_GROUP = `!G:A group.
        finitely_generated_group G <=>
        ?s. FINITE s /\
            s SUBSET group_carrier G /\
            subgroup_generated G s = G`;;

let CYCLIC_IMP_FINITELY_GENERATED_GROUP = `!G:A group. cyclic_group G ==> finitely_generated_group G`;;

let FINITE_IMP_FINITELY_GENERATED_GROUP = `!G:A group. FINITE(group_carrier G) ==> finitely_generated_group G`;;

let TRIVIAL_IMP_FINITELY_GENERATED_GROUP = `!G:A group. trivial_group G ==> finitely_generated_group G`;;

let FINITELY_GENERATED_GROUP_EPIMORPHIC_IMAGE = `!G H (f:A->B).
        group_epimorphism(G,H) f /\ finitely_generated_group G
        ==> finitely_generated_group H`;;

let ISOMORPHIC_GROUP_FINITE_GENERATION = `!(G:A group) (H:B group).
        G isomorphic_group H
        ==> (finitely_generated_group G <=> finitely_generated_group H)`;;

let FINITELY_GENERATED_GROUP_QUOTIENT_GROUP = `!G n:A->bool.
     finitely_generated_group G /\ n normal_subgroup_of G
     ==> finitely_generated_group(quotient_group G n)`;;

let FINITELY_GENERATED_IMP_COUNTABLE_GROUP = `!G:A group. finitely_generated_group G ==> COUNTABLE(group_carrier G)`;;

let FINITELY_GENERATED_PROD_GROUP = `!(G:A group) (H:B group).
        finitely_generated_group(prod_group G H) <=>
        finitely_generated_group G /\ finitely_generated_group H`;;

let FINITELY_GENERATED_PRODUCT_GROUP = `!k (G:K->A group).
        finitely_generated_group(product_group k G) <=>
        FINITE {i | i IN k /\ ~trivial_group(G i)} /\
        !i. i IN k ==> finitely_generated_group(G i)`;;

let FINITELY_GENERATED_SUM_GROUP = `!k (G:K->A group).
        finitely_generated_group(sum_group k G) <=>
        FINITE {i | i IN k /\ ~trivial_group(G i)} /\
        !i. i IN k ==> finitely_generated_group(G i)`;;

let FINITE_GROUP_ACTIONS = `!G s (f:(A->X->X)->B).
        finitely_generated_group G /\ FINITE s /\
        (!a a'. (!g x. g IN group_carrier G /\ x IN s ==> a g x = a' g x)
                ==> f a = f a')
        ==> FINITE {f a | group_action G s a}`;;

let FINITELY_GENERATED_FIXED_INDEX_SUBGROUPS = `!(G:A group) n.
     finitely_generated_group G
     ==> FINITE {h | h subgroup_of G /\
                     {right_coset G h x |x| x IN group_carrier G} HAS_SIZE n}`;;

let FINITELY_GENERATED_FINITE_INDEX_SUBGROUP = `!G h:A->bool.
        finitely_generated_group G /\
        h subgroup_of G /\
        FINITE {right_coset G h x | x | x IN group_carrier G}
        ==> finitely_generated_group(subgroup_generated G h)`;;

let FINITELY_GENERATED_ABELIAN_SUBGROUP_EXPLICIT = `!G s h:A->bool.
        FINITE s /\ s SUBSET group_carrier G /\
        abelian_group G /\ h subgroup_of subgroup_generated G s
        ==> ?t. FINITE t /\ t SUBSET group_carrier G /\
                CARD t <= CARD s /\
                subgroup_generated G t = subgroup_generated G h`;;

let FINITELY_GENERATED_ABELIAN_SUBGROUP = `!G h:A->bool.
        finitely_generated_group G /\ abelian_group G /\ h subgroup_of G
        ==> finitely_generated_group(subgroup_generated G h)`;;

let MAXIMAL_SUBGROUP_EXISTS = `!G:A group.
      finitely_generated_group G /\ ~trivial_group G
      ==> ?h. h subgroup_of G /\ ~(h = group_carrier G) /\
              !h'. h' subgroup_of G /\ h PSUBSET h'
                   ==> h' = group_carrier G`;;

let MAXIMAL_NORMAL_SUBGROUP_EXISTS = `!G:A group.
      finitely_generated_group G /\ ~trivial_group G
      ==> ?h. h normal_subgroup_of G /\ ~(h = group_carrier G) /\
              !h'. h' normal_subgroup_of G /\ h PSUBSET h'
                   ==> h' = group_carrier G`;;

(* ------------------------------------------------------------------------- *)
(* The additive group of integers.                                           *)
(* ------------------------------------------------------------------------- *)

let integer_group = new_definition
 `integer_group = group((:int),&0,(--),(+))`;;

let INTEGER_GROUP = `group_carrier integer_group = (:int) /\
   group_id integer_group = &0 /\
   group_inv integer_group = (--) /\
   group_mul integer_group = (+)`;;

let ABELIAN_INTEGER_GROUP = `abelian_group integer_group`;;

let INFINITE_INTEGER_GROUP = `INFINITE(group_carrier integer_group)`;;

let GROUP_POW_INTEGER_GROUP = `!x n. group_pow integer_group x n = &n * x`;;

let GROUP_ZPOW_INTEGER_GROUP = `!x n. group_zpow integer_group x n = n * x`;;

let GROUP_ELEMENT_ORDER_INTEGER_GROUP = `!n. group_element_order integer_group n = if n = &0 then 1 else 0`;;

let GROUP_ENDOMORPHISM_INTEGER_GROUP_MUL = `!c. group_endomorphism integer_group (\x. c * x)`;;

let GROUP_ENDOMORPHISM_INTEGER_GROUP_EXPLICIT = `!f. group_endomorphism integer_group f ==> f = \x. f(&1) * x`;;

let GROUP_ENDOMORPHISM_INTEGER_GROUP_EQ,
    GROUP_ENDOMORPHISM_INTEGER_GROUP_EQ_ALT =
 (CONJ_PAIR o prove)
 (`(!f. group_endomorphism integer_group f <=> ?c. f = \x. c * x) /\
   (!f. group_endomorphism integer_group f <=> ?!c. f = \x. c * x)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(!c. P(m c)) /\ (!f. P f ==> ?c. f = m c) /\
    (!c d. m c = m d ==> c = d)
    ==> (P f <=> ?c. f = m c) /\ (P f <=> ?!c. f = m c)`) THEN
  REWRITE_TAC[GROUP_ENDOMORPHISM_INTEGER_GROUP_MUL] THEN CONJ_TAC THENL
   [X_GEN_TAC `f:int->int` THEN DISCH_TAC THEN
    EXISTS_TAC `(f:int->int) (&1)` THEN
   MATCH_MP_TAC GROUP_ENDOMORPHISM_INTEGER_GROUP_EXPLICIT THEN
   ASM_REWRITE_TAC[];
   REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[INT_MUL_RID]]);;

let GROUP_HOMOMORPHISM_GROUP_ZPOW = `!G x:A. x IN group_carrier G
           ==> group_homomorphism(integer_group,G) (group_zpow G x)`;;

let GROUP_EPIMORPHISM_GROUP_ZPOW = `!G x:A. x IN group_carrier G
           ==> group_epimorphism (integer_group,subgroup_generated G {x})
                                 (group_zpow G x)`;;

let GROUP_ISOMORPHISM_GROUP_ZPOW = `!G x:A. INFINITE(group_carrier(subgroup_generated G {x})) /\
           x IN group_carrier G
           ==> group_isomorphism (integer_group,subgroup_generated G {x})
                                 (group_zpow G x)`;;

let ISOMORPHIC_GROUP_INFINITE_CYCLIC_INTEGER = `!G:A group.
        cyclic_group G /\ INFINITE(group_carrier G)
        ==> G isomorphic_group integer_group`;;

let ISOMORPHIC_INFINITE_CYCLIC_GROUPS = `!(G:A group) (H:B group).
        cyclic_group G /\ INFINITE(group_carrier G) /\
        cyclic_group H /\ INFINITE(group_carrier H)
        ==> G isomorphic_group H`;;

(* ------------------------------------------------------------------------- *)
(* Additive group of integers modulo n (n = 0 gives just the integers).      *)
(* ------------------------------------------------------------------------- *)

let integer_mod_group = new_definition
  `integer_mod_group n =
     if n = 0 then integer_group else
     group({m | &0 <= m /\ m < &n},
           &0,
           (\a. --a rem &n),
           (\a b. (a + b) rem &n))`;;

let INTEGER_MOD_GROUP = `(group_carrier(integer_mod_group 0) = (:int)) /\
   (!n. 0 < n
        ==> group_carrier(integer_mod_group n) = {m | &0 <= m /\ m < &n}) /\
   (!n. group_id(integer_mod_group n) = &0) /\
   (!n. group_inv(integer_mod_group n) = \a. --a rem &n) /\
   (!n. group_mul(integer_mod_group n) = \a b. (a + b) rem &n)`;;

let INTEGER_MOD_GROUP_TRIVIAL = `integer_mod_group 0 = integer_group`;;

let GROUP_CARRIER_INTEGER_MOD_GROUP = `!n. group_carrier (integer_mod_group n) = IMAGE (\x. x rem &n) (:int)`;;

let GROUP_POW_INTEGER_MOD_GROUP = `!n x m. group_pow (integer_mod_group n) x m = (&m * x) rem &n`;;

let GROUP_ZPOW_INTEGER_MOD_GROUP = `!n x m. group_zpow (integer_mod_group n) x m = (m * x) rem &n`;;

let ABELIAN_INTEGER_MOD_GROUP = `!n. abelian_group(integer_mod_group n)`;;

let INTEGER_MOD_GROUP_0 = `!n. &0 IN group_carrier(integer_mod_group n)`;;

let INTEGER_MOD_GROUP_1R = `!n x. (x rem &n) IN group_carrier(integer_mod_group n)`;;

let INTEGER_MOD_GROUP_1 = `!n. &1 IN group_carrier(integer_mod_group n) <=> ~(n = 1)`;;

let GROUP_HOMOMORPHISM_PROD_INTEGER_MOD_GROUP = `!m n.
        group_homomorphism
         (integer_mod_group (m * n),
          prod_group (integer_mod_group m) (integer_mod_group n))
         (\a. (a rem &m),(a rem &n))`;;

let TRIVIAL_INTEGER_MOD_GROUP = `!n. trivial_group(integer_mod_group n) <=> n = 1`;;

let NON_TRIVIAL_INTEGER_GROUP = `~(trivial_group integer_group)`;;

let GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP_1 = `!n. group_element_order (integer_mod_group n) (&1) = n`;;

let GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP_1R = `!n. group_element_order (integer_mod_group n) (&1 rem &n) = n`;;

let GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP = `!n m. group_element_order (integer_mod_group n) (&m) =
         if m = 0 /\ n = 0 then 1 else n DIV gcd(n,m)`;;

let INTEGER_MOD_SUBGROUP_GENERATED_BY_1R = `!n. subgroup_generated (integer_mod_group n) {&1 rem &n} =
       integer_mod_group n`;;

let INTEGER_MOD_SUBGROUP_GENERATED_BY_1 = `!n. subgroup_generated (integer_mod_group n) {&1} =
       integer_mod_group n`;;

let CYCLIC_GROUP_INTEGER_MOD_GROUP = `!n. cyclic_group(integer_mod_group n)`;;

let CYCLIC_INTEGER_GROUP = `cyclic_group integer_group`;;

let FINITE_INTEGER_MOD_GROUP = `!n. FINITE(group_carrier(integer_mod_group n)) <=> ~(n = 0)`;;

let GROUP_EPIMORPHISM_INTEGER_MOD_GROUP_ZPOW = `!n. ~(n = 1)
       ==> group_epimorphism (integer_group,integer_mod_group n)
                             (group_zpow (integer_mod_group n) (&1))`;;

let GROUP_ISOMORPHISM_GROUP_ZPOW_GEN = `!G x:A.
        x IN group_carrier G
        ==> group_isomorphism (integer_mod_group (group_element_order G x),
                               subgroup_generated G {x})
                              (group_zpow G x)`;;

let ISOMORPHIC_GROUP_CYCLIC_INTEGER = `!G:A group. cyclic_group G <=> ?n. G isomorphic_group integer_mod_group n`;;

let ORDER_INTEGER_MOD_GROUP = `!n. ~(n = 0) ==> CARD(group_carrier(integer_mod_group n)) = n`;;

let ISOMORPHIC_FINITE_CYCLIC_INTEGER_MOD_GROUP = `!G:A group.
        cyclic_group G /\ FINITE(group_carrier G)
        ==> G isomorphic_group integer_mod_group (CARD(group_carrier G))`;;

let ISOMORPHIC_GROUP_INTEGER_MOD_GROUP = `(!(G:A group) n.
        G isomorphic_group integer_mod_group n <=>
        cyclic_group G /\
        (n = 0 /\ INFINITE(group_carrier G) \/
         ~(n = 0) /\ (group_carrier G) HAS_SIZE n)) /\
   (!(G:A group) n.
        integer_mod_group n isomorphic_group G <=>
        cyclic_group G /\
        (n = 0 /\ INFINITE(group_carrier G) \/
         ~(n = 0) /\ (group_carrier G) HAS_SIZE n))`;;

let ISOMORPHIC_INTEGER_MOD_GROUPS = `!m n. integer_mod_group m isomorphic_group integer_mod_group n <=>
         m = n`;;

let ISOMORPHIC_FINITE_CYCLIC_GROUPS = `!(G:A group) (H:B group).
        cyclic_group G /\ cyclic_group H /\
        FINITE(group_carrier G) /\ FINITE(group_carrier H) /\
        CARD(group_carrier G) = CARD(group_carrier H)
        ==> G isomorphic_group H`;;

let CYCLIC_IMP_COUNTABLE_GROUP = `!G:A group. cyclic_group G ==> COUNTABLE(group_carrier G)`;;

let SUBGROUP_GENERATED_ELEMENT_ORDER = `!G a:A.
        FINITE(group_carrier G) /\ a IN group_carrier G
        ==> (subgroup_generated G {a} = G <=>
             group_element_order G a = CARD(group_carrier G))`;;

let CYCLIC_GROUP_ELEMENT_ORDER = `!G:A group.
        FINITE(group_carrier G)
        ==> (cyclic_group G <=>
             ?a. a IN group_carrier G /\
                 group_element_order G a = CARD(group_carrier G))`;;

let [CYCLIC_PROD_INTEGER_MOD_GROUP;
     ISOMORPHIC_PROD_INTEGER_MOD_GROUP;
     GROUP_ISOMORPHISM_PROD_INTEGER_MOD_GROUP] = (CONJUNCTS o prove)
 (`(!m n. cyclic_group (prod_group (integer_mod_group m) (integer_mod_group n))
          <=> coprime(m,n)) /\
   (!m n.
        prod_group (integer_mod_group m) (integer_mod_group n) isomorphic_group
        integer_mod_group (m * n) <=>
        coprime(m,n)) /\
   (!m n.
        group_isomorphism
         (integer_mod_group (m * n),
          prod_group (integer_mod_group m) (integer_mod_group n))
         (\a. (a rem &m),(a rem &n)) <=>
        coprime(m,n))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(r ==> q) /\ (q ==> p) /\ (p ==> c) /\ (c ==> r)
    ==> (p <=> c) /\ (q <=> c) /\ (r <=> c)`) THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[GROUP_ISOMORPHISM_IMP_ISOMORPHIC];
    DISCH_THEN(MP_TAC o MATCH_MP ISOMORPHIC_GROUP_CYCLICITY) THEN
    REWRITE_TAC[CYCLIC_GROUP_INTEGER_MOD_GROUP];
    GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[CYCLIC_GROUP] THEN
    REWRITE_TAC[MESON[] `~(?x. P x /\ Q x) <=> !x. P x ==> ~Q x`] THEN
    SIMP_TAC[FORALL_PAIR_THM; PROD_GROUP; IN_CROSS;
             GROUP_ZPOW_INTEGER_MOD_GROUP; GROUP_ZPOW_PROD_GROUP] THEN
    REWRITE_TAC[GROUP_CARRIER_INTEGER_MOD_GROUP] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN
    MATCH_MP_TAC(SET_RULE `!z. z IN s /\ ~(z IN t) ==> ~(s = t)`) THEN
    REWRITE_TAC[EXISTS_PAIR_THM; EXISTS_IN_IMAGE; RIGHT_EXISTS_AND_THM;
                IN_CROSS; GSYM CONJ_ASSOC; IN_UNIV; IN_ELIM_THM] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[PAIR_EQ; INT_REM_EQ] THEN
    POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[num_coprime; NOT_EXISTS_THM] THEN MESON_TAC[INTEGER_RULE
     `(x * a == &1) (mod m) /\ (x * b == &1) (mod n) /\
      (y * a == &0) (mod m) /\ (y * b == &1) (mod n)
      ==> coprime(m,n)`];
    REWRITE_TAC[GROUP_ISOMORPHISM_SUBSET] THEN
    REWRITE_TAC[GROUP_HOMOMORPHISM_PROD_INTEGER_MOD_GROUP] THEN
    REWRITE_TAC[PROD_GROUP; FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    ASM_CASES_TAC `m = 0` THENL
     [ASM_SIMP_TAC[INT_REM_0; MULT_CLAUSES; INT_REM_1;
                   NUMBER_RULE `coprime(0,n) <=> n = 1`] THEN
      SIMP_TAC[INTEGER_MOD_GROUP; ARITH; IN_UNIV; IN_ELIM_THM] THEN
      REWRITE_TAC[UNWIND_THM2] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `n = 0` THENL
     [ASM_SIMP_TAC[INT_REM_0; MULT_CLAUSES; INT_REM_1;
                   NUMBER_RULE `coprime(n,0) <=> n = 1`] THEN
      SIMP_TAC[INTEGER_MOD_GROUP; ARITH; IN_UNIV; IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[INTEGER_MOD_GROUP; LE_1; MULT_EQ_0] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THENL
     [STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_coprime]) THEN
      DISCH_THEN(MP_TAC o SPECL [`a:int`; `b:int`] o MATCH_MP (INTEGER_RULE
         `coprime(m:int,n)
          ==> !a b. ?c. (c == a) (mod m) /\ (c == b) (mod n)`)) THEN
      ASM_SIMP_TAC[GSYM INT_REM_EQ; INT_REM_LT] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `c rem &(m * n)` THEN
      REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      ASM_SIMP_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LT; MULT_EQ_0; LE_1] THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_MUL; INT_REM_REM_MUL];
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_coprime]) THEN
      DISCH_THEN(MP_TAC o SPECL [`a:int`; `b:int`] o MATCH_MP (INTEGER_RULE
         `coprime(m:int,n)
          ==> !a b. (a == b) (mod m) /\ (a == b) (mod n)
        ==> (a == b) (mod (m * n))`)) THEN
      ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN
      MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN MATCH_MP_TAC INT_REM_LT THEN
      ASM_REWRITE_TAC[INT_OF_NUM_MUL]]]);;

let CYCLIC_PROD_GROUP = `!(G:A group) (H:B group).
        cyclic_group (prod_group G H) <=>
        cyclic_group G /\ cyclic_group H /\
        (trivial_group G \/
         trivial_group H \/
         FINITE(group_carrier G) /\ FINITE(group_carrier H) /\
         coprime(CARD(group_carrier G),CARD(group_carrier H)))`;;

let CYCLIC_PRIME_ORDER_GROUP = `!G (a:A).
        FINITE (group_carrier G) /\
        (CARD(group_carrier G) = 1 \/ prime(CARD(group_carrier G))) /\
        a IN group_carrier G /\ ~(a = group_id G)
        ==> subgroup_generated G {a} = G`;;

let GROUP_ELEMENT_ORDER_PRIME = `!G a:A. prime p /\ (group_carrier G) HAS_SIZE p /\ a IN group_carrier G
           ==> group_element_order G a =
               if a = group_id G then 1 else CARD(group_carrier G)`;;

let GENERATOR_INTEGER_MOD_GROUP = `!n a. subgroup_generated (integer_mod_group n) {a} = integer_mod_group n <=>
         (n <= 1 \/ &0 <= a /\ a < &n) /\ coprime(&n,a)`;;

let CYCLIC_GROUP_PRIME_ORDER_EQ = `!(G:A group).
        (!a. a IN group_carrier G /\ ~(a = group_id G)
             ==> subgroup_generated G {a} = G) <=>
        FINITE(group_carrier G) /\
        (CARD (group_carrier G) = 1 \/ prime (CARD (group_carrier G)))`;;

(* ------------------------------------------------------------------------- *)
(* p-groups, Sylow's theorems, Cauchy's theorem etc.                         *)
(* ------------------------------------------------------------------------- *)

let pgroup = new_definition
 `pgroup s (G:A group) <=>
        !p x. prime p /\
              x IN group_carrier G /\
              p divides group_element_order G x
              ==> p IN s`;;

let PGROUP_MONOMORPHIC_PREIMAGE = `!G H (f:A->B) s. group_monomorphism (G,H) f /\ pgroup s H ==> pgroup s G`;;

let PGROUP_EPIMORPHIC_IMAGE = `!G H (f:A->B) s. group_epimorphism (G,H) f /\ pgroup s G ==> pgroup s H`;;

let PGROUP_QUOTIENT_GROUP = `!(G:A group) n s.
      n normal_subgroup_of G /\ pgroup s G ==> pgroup s (quotient_group G n)`;;

let PGROUP_SUBGROUP_GENERATED = `!(G:A group) s h.
        pgroup s G ==> pgroup s (subgroup_generated G h)`;;

let PGROUP_PROD_GROUP = `!(G:A group) (H:A group) s.
        pgroup s (prod_group G H) <=> pgroup s G /\ pgroup s H`;;

let PGROUP_EMPTY = `!G:A group. pgroup {} G <=> trivial_group G`;;

let PGROUP_MONO = `!(G:A group) s t. pgroup s G /\ s SUBSET t ==> pgroup t G`;;

let PGROUP_SUM_GROUP = `!k (G:K->A group) s.
        pgroup s (sum_group k G) <=> !i. i IN k ==> pgroup s (G i)`;;

let PGROUP_SING = `!(G:A group) p.
     prime p
     ==> (pgroup {p} G <=>
          !x. x IN group_carrier G ==> ?k. group_element_order G x = p EXP k)`;;

let SYLOW_THEOREM_COUNT_MOD = `!(G:A group) p k.
        FINITE(group_carrier G) /\
        prime p /\
        p EXP k divides CARD(group_carrier G)
        ==> (CARD {h | h subgroup_of G /\ CARD h = p EXP k} == 1) (mod p)`;;

let SYLOW_THEOREM = `!(G:A group) p k.
        FINITE(group_carrier G) /\
        prime p /\
        p EXP k divides CARD(group_carrier G)
        ==> ?h. h subgroup_of G /\ CARD h = p EXP k`;;

let CAUCHY_GROUP_THEOREM = `!(G:A group) p.
        FINITE(group_carrier G) /\ prime p /\ p divides CARD(group_carrier G)
        ==> ?x. x IN group_carrier G /\ group_element_order G x = p`;;

let PRIME_DIVIDES_GROUP_ORDER = `!(G:A group) p.
    FINITE(group_carrier G) /\ prime p
    ==> ((?x. x IN group_carrier G /\ p divides (group_element_order G x)) <=>
         p divides CARD(group_carrier G))`;;

let COPRIME_GROUP_ORDER = `!(G:A group) n.
    FINITE(group_carrier G)
    ==> ((!x. x IN group_carrier G ==> coprime(group_element_order G x,n)) <=>
         coprime(CARD(group_carrier G),n))`;;

let FINITE_PGROUP = `!s (G:A group).
        FINITE(group_carrier G)
        ==> (pgroup s G <=>
             !p. prime p /\ p divides CARD(group_carrier G) ==> p IN s)`;;

let FINITE_PGROUP_SING = `!(G:A group) p.
     FINITE(group_carrier G) /\ prime p
     ==> (pgroup {p} G <=> ?k. CARD(group_carrier G) = p EXP k)`;;

let FINITE_AND_PGROUP_SING = `!(G:A group) p.
     prime p
     ==> (FINITE(group_carrier G) /\ pgroup {p} G <=>
          ?k. (group_carrier G) HAS_SIZE (p EXP k))`;;

let FINITE_GROUP_POW_INJECTIVE_EQ = `!(G:A group) n.
        FINITE(group_carrier G)
        ==> ((!x y. x IN group_carrier G /\ y IN group_carrier G /\
                    group_pow G x n = group_pow G y n
                    ==> x = y) <=>
             coprime(n,CARD(group_carrier G)))`;;

let FINITE_GROUP_ZPOW_INJECTIVE_EQ = `!(G:A group) n.
        FINITE(group_carrier G)
        ==> ((!x y. x IN group_carrier G /\ y IN group_carrier G /\
                    group_zpow G x n = group_zpow G y n
                    ==> x = y) <=>
             coprime(n,&(CARD(group_carrier G))))`;;

let FINITE_GROUP_POW_SURJECTIVE_EQ = `!(G:A group) n.
        FINITE(group_carrier G)
        ==> ((!x. x IN group_carrier G
                  ==> ?y. y IN group_carrier G /\ group_pow G y n = x) <=>
             coprime(n,CARD(group_carrier G)))`;;

let FINITE_GROUP_ZPOW_SURJECTIVE_EQ = `!(G:A group) n.
        FINITE(group_carrier G)
        ==> ((!x. x IN group_carrier G
                  ==> ?y. y IN group_carrier G /\ group_zpow G y n = x) <=>
             coprime(n,&(CARD(group_carrier G))))`;;

let FINITE_GROUP_ZROOT_EXISTS = `!G n x:A.
        FINITE(group_carrier G) /\
        coprime(n,&(CARD(group_carrier G))) /\
        x IN group_carrier G
        ==> ?y. y IN group_carrier G /\ group_zpow G y n = x`;;

let FINITE_GROUP_ROOT_EXISTS = `!G n x:A.
        FINITE(group_carrier G) /\
        coprime(n,CARD(group_carrier G)) /\
        x IN group_carrier G
        ==> ?y. y IN group_carrier G /\ group_pow G y n = x`;;

let ABELIAN_GROUP_MONOMORPHISM_POWERING_EQ = `!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G)
        ==> (group_monomorphism (G,G) (\x. group_pow G x n) <=>
             coprime(n,CARD(group_carrier G)))`;;

let ABELIAN_GROUP_MONOMORPHISM_POWERING = `!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G) /\
        coprime(n,CARD(group_carrier G))
        ==> group_monomorphism (G,G) (\x. group_pow G x n)`;;

let ABELIAN_GROUP_ISOMORPHISM_POWERING_EQ = `!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G)
        ==> (group_isomorphism (G,G) (\x. group_pow G x n) <=>
             coprime(n,CARD(group_carrier G)))`;;

let ABELIAN_GROUP_ISOMORPHISM_POWERING = `!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G) /\
        coprime(n,CARD(group_carrier G))
        ==> group_isomorphism (G,G) (\x. group_pow G x n)`;;

let ABELIAN_GROUP_EPIMORPHISM_POWERING_EQ = `!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G)
        ==> (group_epimorphism (G,G) (\x. group_pow G x n) <=>
             coprime(n,CARD(group_carrier G)))`;;

let ABELIAN_GROUP_EPIMORPHISM_POWERING = `!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G) /\
        coprime(n,CARD(group_carrier G))
        ==> group_epimorphism (G,G) (\x. group_pow G x n)`;;

let PGROUP_ACTION_FIXPOINTS = `!G s (a:A->X->X) p.
        group_action G s a /\ FINITE s /\
        prime p /\ FINITE(group_carrier G) /\ pgroup {p} G
        ==> (CARD {x | x IN s /\ !g. g IN group_carrier G ==> a g x = x} ==
             CARD s) (mod p)`;;

let PGROUP_ACTION_FIXPOINT = `!G s (a:A->X->X) p.
        group_action G s a /\
        prime p /\ FINITE(group_carrier G) /\ pgroup {p} G /\
        FINITE s /\ ~(p divides CARD s)
        ==> ?x. x IN s /\ !g. g IN group_carrier G ==> a g x = x`;;

let SYLOW_THEOREM_CONJUGATE_GEN = `!(G:A group) p k h j.
        prime p /\
        h subgroup_of G /\
        FINITE {left_coset G x h | x | x IN group_carrier G} /\
        ~(p divides CARD {left_coset G x h | x | x IN group_carrier G}) /\
        j subgroup_of G /\ FINITE j /\ CARD j = p EXP k
        ==> ?a. a IN group_carrier G /\
                j SUBSET IMAGE (group_conjugation G a) h`;;

let SYLOW_THEOREM_CONJUGATE_SUBSET = `!(G:A group) p k l h j.
        FINITE(group_carrier G) /\ prime p /\
        ~(p EXP (k + 1) divides CARD(group_carrier G)) /\
        h subgroup_of G /\ CARD h = p EXP k /\
        j subgroup_of G /\ CARD j = p EXP l
        ==> ?a. a IN group_carrier G /\
                j SUBSET IMAGE (group_conjugation G a) h`;;

let SYLOW_THEOREM_CONJUGATE_ALT = `!(G:A group) p k h h'.
        FINITE(group_carrier G) /\ prime p /\
        ~(p EXP (k + 1) divides CARD(group_carrier G)) /\
        h subgroup_of G /\ CARD h = p EXP k /\
        h' subgroup_of G /\ CARD h' = p EXP k
        ==> group_conjugate G h h'`;;

let SYLOW_THEOREM_CONJUGATE = `!(G:A group) p k h h'.
        FINITE(group_carrier G) /\ prime p /\
        index p (CARD(group_carrier G)) = k /\
        h subgroup_of G /\ CARD h = p EXP k /\
        h' subgroup_of G /\ CARD h' = p EXP k
        ==> group_conjugate G h h'`;;

let SYLOW_THEOREM_CONJUGATE_EQ = `!(G:A group) p k h h'.
      FINITE(group_carrier G) /\ prime p /\
      index p (CARD(group_carrier G)) = k /\
      h subgroup_of G /\ CARD h = p EXP k
      ==> (h' subgroup_of G /\ CARD h' = p EXP k <=> group_conjugate G h h')`;;

let SYLOW_THEOREM_PGROUP_SUPERSET = `!G p k (h:A->bool).
        FINITE(group_carrier G) /\ prime p /\
        h subgroup_of G /\ CARD h = p EXP k
        ==> ?h'. h' subgroup_of G /\ h SUBSET h' /\
                 CARD h' = p EXP (index p (CARD(group_carrier G)))`;;

let SYLOW_THEOREM_NORMAL_UNIQUE = `!(G:A group) p k h h'.
      FINITE(group_carrier G) /\ prime p /\
      index p (CARD(group_carrier G)) = k /\
      h normal_subgroup_of G /\ CARD h = p EXP k
      ==> (h' subgroup_of G /\ CARD h' = p EXP k <=> h' = h)`;;

let SYLOW_THEOREM_COUNT_NORMALIZER = `!(G:A group) h p k.
        FINITE(group_carrier G) /\ prime p /\
        index p (CARD(group_carrier G)) = k /\
        h subgroup_of G /\ CARD h = p EXP k
        ==> CARD {h | h subgroup_of G /\ CARD h = p EXP k} =
            CARD(group_carrier G) DIV CARD(group_normalizer G h)`;;

let SYLOW_THEOREM_COUNT_NORMALIZER_MUL = `!(G:A group) h p k.
        FINITE(group_carrier G) /\ prime p /\
        index p (CARD(group_carrier G)) = k /\
        h subgroup_of G /\ CARD h = p EXP k
        ==> CARD {h | h subgroup_of G /\ CARD h = p EXP k} *
            CARD(group_normalizer G h) =
            CARD(group_carrier G)`;;

let SYLOW_THEOREM_NORMAL_UNIQUE_EQ = `!G p k h:A->bool.
        FINITE (group_carrier G) /\
        prime p /\
        index p (CARD (group_carrier G)) = k /\
        h subgroup_of G /\
        CARD h = p EXP k
        ==> ((!h'. h' subgroup_of G /\ CARD h' = p EXP k <=> h' = h) <=>
             h normal_subgroup_of G)`;;

let SYLOW_THEOREM_UNIQUE = `!(G:A group) p k.
        FINITE(group_carrier G) /\
        prime p /\
        index p (CARD(group_carrier G)) = k
        ==> ((?!h. h subgroup_of G /\ CARD h = p EXP k) <=>
             (?h. h normal_subgroup_of G /\ CARD h = p EXP k))`;;

let SYLOW_THEOREM_COUNT_DIVISOR = `!(G:A group) p k.
        FINITE(group_carrier G) /\ prime p /\
        index p (CARD(group_carrier G)) = k
        ==> CARD {h | h subgroup_of G /\ CARD h = p EXP k}
            divides (CARD(group_carrier G)) DIV (p EXP k)`;;

let PGROUP_NONTRIVIAL_CENTRE_GEN = `!G (n:A->bool) p.
        prime p /\ FINITE(group_carrier G) /\ pgroup {p} G /\
        n normal_subgroup_of G /\ ~(n = {group_id G})
        ==> {group_id G} PSUBSET
            (group_centralizer G (group_carrier G) INTER n)`;;

let PGROUP_NONTRIVIAL_CENTRE = `!(G:A group) p k.
        prime p /\ ~(k = 0) /\ (group_carrier G) HAS_SIZE (p EXP k)
        ==> {group_id G} PSUBSET (group_centralizer G (group_carrier G))`;;

let PGROUP_DIVIDES_NORMALIZER_QUOTIENT = `!G p k h:A->bool.
        FINITE(group_carrier G) /\
        prime p /\
        h subgroup_of G /\ CARD h = p EXP k /\
        p divides CARD(group_carrier G) DIV CARD h
        ==> p divides CARD(group_normalizer G h) DIV CARD h`;;

let PGROUP_SUBGROUP_PSUBSET_NORMALIZER = `!G p h:A->bool.
        prime p /\ FINITE(group_carrier G) /\ pgroup {p} G /\
        h subgroup_of G /\ ~(h = group_carrier G)
        ==> h PSUBSET group_normalizer G h`;;

let PGROUP_MAXIMAL_NORMAL_SUBGROUP_OF = `!G p h:A->bool.
        prime p /\ FINITE(group_carrier G) /\ pgroup {p} G /\
        h subgroup_of G /\
        (!h'. h' subgroup_of G /\ h PSUBSET h' ==> h' = group_carrier G)
        ==> h normal_subgroup_of G`;;

let PGROUP_FRATTINI = `!(G:A group) p k h j.
        prime p /\
        FINITE j /\ j normal_subgroup_of G /\
        h SUBSET j /\ h subgroup_of G /\
        index p (CARD j) = k /\ CARD h = p EXP k
        ==> group_setmul G (group_normalizer G h) j = group_carrier G`;;

let PGROUP_SELF_NORMALIZER = `!G p k s h:A->bool.
        FINITE(group_carrier G) /\
        prime p /\
        index p (CARD(group_carrier G)) = k /\
        s subgroup_of G /\ CARD s = p EXP k /\
        h subgroup_of G /\ group_normalizer G s SUBSET h
        ==> group_normalizer G h = h`;;

let PGROUP_NORMALIZER_NORMALIZER = `!G p k h:A->bool.
        FINITE(group_carrier G) /\
        prime p /\
        index p (CARD(group_carrier G)) = k /\
        h subgroup_of G /\ CARD h = p EXP k
        ==> group_normalizer G (group_normalizer G h) = group_normalizer G h`;;

(* ------------------------------------------------------------------------- *)
(* Theorems related to "internal" direct sums.                               *)
(* ------------------------------------------------------------------------- *)

let GROUP_DISJOINT_SUM_ALT = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (g INTER h SUBSET {group_id G} <=> g INTER h = {group_id G})`;;

let GROUP_DISJOINT_SUM_ID = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (g INTER h SUBSET {group_id G} <=>
             !x y. x IN g /\ y IN h /\ group_mul G x y = group_id G
                   ==> x = group_id G /\ y = group_id G)`;;

let GROUP_DISJOINT_SUM_CANCEL = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (g INTER h SUBSET {group_id G} <=>
             !x x' y y'. x IN g /\ x' IN g /\ y IN h /\ y' IN h /\
                         group_mul G x y = group_mul G x' y'
                         ==> x = x' /\ y = y')`;;

let GROUP_SUM_COMMUTING_IMP_NORMAL = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G /\
        group_carrier G SUBSET group_setmul G g h /\
        (!x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)
        ==> g normal_subgroup_of G /\ h normal_subgroup_of G`;;

let GROUP_SUM_NORMAL_IMP_COMMUTING = `!G g h:A->bool.
        g normal_subgroup_of G /\ h normal_subgroup_of G /\
        g INTER h SUBSET {group_id G}
        ==> !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x`;;

let GROUP_SUM_NORMAL_EQ_COMMUTING = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G /\
        group_carrier G SUBSET group_setmul G g h /\
        g INTER h SUBSET {group_id G}
        ==> (g normal_subgroup_of G /\ h normal_subgroup_of G <=>
             !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`;;

let GROUP_HOMOMORPHISM_GROUP_MUL_GEN = `!G g h:A->bool.
        group_homomorphism
            (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
            (\(x,y). group_mul G x y) <=>
        !x y. x IN group_carrier G /\ x IN g /\
              y IN group_carrier G /\ y IN h
              ==> group_mul G x y = group_mul G y x`;;

let GROUP_HOMOMORPHISM_GROUP_MUL_EQ = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_homomorphism
              (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
              (\(x,y). group_mul G x y) <=>
              !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`;;

let GROUP_HOMOMORPHISM_GROUP_MUL = `!G g h:A->bool.
        abelian_group G
        ==> group_homomorphism
              (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
              (\(x,y). group_mul G x y)`;;

let GROUP_EPIMORPHISM_GROUP_MUL_EQ = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_epimorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             group_setmul G g h = group_carrier G /\
             !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`;;

let GROUP_MONOMORPHISM_GROUP_MUL_EQ = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_monomorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             g INTER h = {group_id G} /\
             !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`;;

let GROUP_ISOMORPHISM_GROUP_MUL_ALT = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_isomorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             g INTER h = {group_id G} /\
             group_setmul G g h = group_carrier G /\
             !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`;;

let GROUP_ISOMORPHISM_GROUP_MUL_EQ = `!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_isomorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             g normal_subgroup_of G /\ h normal_subgroup_of G /\
             g INTER h = {group_id G} /\
             group_setmul G g h = group_carrier G)`;;

let GROUP_ISOMORPHISM_GROUP_MUL_GEN = `!G g h:A->bool.
        g normal_subgroup_of G /\ h normal_subgroup_of G
        ==> (group_isomorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             g INTER h SUBSET {group_id G} /\
             group_setmul G g h = group_carrier G)`;;

let GROUP_ISOMORPHISM_GROUP_MUL = `!G g h:A->bool.
        abelian_group G /\ g subgroup_of G /\ h subgroup_of G
        ==> (group_isomorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             g INTER h SUBSET {group_id G} /\
             group_setmul G g h = group_carrier G)`;;

let ISOMORPHIC_PROD_GROUP_SUBGROUP_GENERATED = `!G g h:A->bool.
        g normal_subgroup_of G /\ h normal_subgroup_of G /\
        g INTER h = {group_id G}
        ==> prod_group (subgroup_generated G g) (subgroup_generated G h)
            isomorphic_group subgroup_generated G (group_setmul G g h)`;;

let GROUP_INTER_IM_KER = `!(f:A->B) (g:B->C) G H K.
        group_homomorphism(G,H) f /\
        group_homomorphism(H,K) g /\
        group_monomorphism(G,K) (g o f)
        ==> (group_image(G,H) f) INTER (group_kernel(H,K) g) =
            {group_id H}`;;

let GROUP_SUM_IM_KER = `!(f:A->B) (g:B->C) G H K.
        group_homomorphism(G,H) f /\
        group_homomorphism(H,K) g /\
        group_epimorphism(G,K) (g o f)
        ==> group_setmul H (group_image(G,H) f) (group_kernel(H,K) g) =
            group_carrier H`;;

let GROUP_SUM_KER_IM = `!(f:A->B) (g:B->C) G H K.
        group_homomorphism(G,H) f /\
        group_homomorphism(H,K) g /\
        group_epimorphism(G,K) (g o f)
        ==> group_setmul H (group_kernel(H,K) g) (group_image(G,H) f) =
            group_carrier H`;;

let GROUP_SEMIDIRECT_SUM_IM_KER = `!(f:A->B) (g:B->C) G H K.
      group_homomorphism(G,H) f /\
      group_homomorphism(H,K) g /\
      group_isomorphism(G,K) (g o f)
      ==> (group_image(G,H) f) INTER (group_kernel(H,K) g) = {group_id H} /\
          group_setmul H (group_image(G,H) f) (group_kernel(H,K) g) =
          group_carrier H`;;

let GROUP_SEMIDIRECT_SUM_KER_IM = `!(f:A->B) (g:B->C) G H K.
      group_homomorphism(G,H) f /\
      group_homomorphism(H,K) g /\
      group_isomorphism(G,K) (g o f)
      ==> (group_kernel(H,K) g) INTER (group_image(G,H) f) = {group_id H} /\
           group_setmul H (group_kernel(H,K) g) (group_image(G,H) f) =
           group_carrier H`;;

let GROUP_ISOMORPHISM_GROUP_MUL_IM_KER = `!(f:A->B) (g:B->C) G H K.
        abelian_group H /\
        group_homomorphism(G,H) f /\
        group_homomorphism(H,K) g /\
        group_isomorphism(G,K) (g o f)
        ==> group_isomorphism
              (prod_group (subgroup_generated H (group_image(G,H) f))
                          (subgroup_generated H (group_kernel(H,K) g)),H)
              (\(x,y). group_mul H x y)`;;

let GROUP_ISOMORPHISM_GROUP_MUL_KER_IM = `!(f:A->B) (g:B->C) G H K.
        abelian_group H /\
        group_homomorphism(G,H) f /\
        group_homomorphism(H,K) g /\
        group_isomorphism(G,K) (g o f)
        ==> group_isomorphism
              (prod_group (subgroup_generated H (group_kernel(H,K) g))
                          (subgroup_generated H (group_image(G,H) f)),H)
              (\(x,y). group_mul H x y)`;;

(* ------------------------------------------------------------------------- *)
(* Internal versus external direct sums over an arbitrary indexing set.      *)
(* ------------------------------------------------------------------------- *)

let GROUP_HOMOMORPHISM_GROUP_SUM_GEN = `!k l G (h:K->A->bool).
      k SUBSET l
      ==> (group_homomorphism (sum_group l (\i. subgroup_generated G (h i)),G)
                              (group_sum G k) <=>
           pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                                 y IN group_carrier G /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k)`;;

let GROUP_HOMOMORPHISM_GROUP_SUM_EQ = `!k l G (h:K->A->bool).
      k SUBSET l /\
      (!i. i IN k ==> (h i) subgroup_of G)
      ==> (group_homomorphism (sum_group l (\i. subgroup_generated G (h i)),G)
                              (group_sum G k) <=>
           pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k)`;;

let GROUP_HOMOMORPHISM_GROUP_SUM = `!k G (h:K->A->bool).
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k
        ==> group_homomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                               (group_sum G k)`;;

let GROUP_HOMOMORPHISM_ABELIAN_GROUP_SUM = `!k G (h:K->A->bool).
        abelian_group G
        ==> group_homomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                               (group_sum G k)`;;

let ABELIAN_GROUP_HOMOMORPHISM_GROUP_SUM = `!(f:K->A->B) k A B.
        abelian_group B /\
        (!i. i IN k ==> group_homomorphism (A i,B) (f i))
        ==> group_homomorphism (sum_group k A,B)
             (\x. group_sum B k (\i. (f i) (x i)))`;;

let SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN = `!k l G (h:K->A->bool).
        k SUBSET l
        ==> (group_epimorphism (sum_group l (\i. subgroup_generated G (h i)),
                                subgroup_generated G (UNIONS {h i | i IN k}))
                               (group_sum G k) <=>
             pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                                   y IN group_carrier G /\ y IN (h j)
                                   ==> group_mul G x y = group_mul G y x) k)`;;

let SUBGROUP_EPIMORPHISM_GROUP_SUM_EQ = `!k l G (h:K->A->bool).
      k SUBSET l /\
      (!i. i IN k ==> (h i) subgroup_of G)
      ==> (group_epimorphism (sum_group l (\i. subgroup_generated G (h i)),
                              subgroup_generated G (UNIONS {h i | i IN k}))
                              (group_sum G k) <=>
           pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k)`;;

let SUBGROUP_EPIMORPHISM_GROUP_SUM = `!k G (h:K->A->bool).
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k
        ==> group_epimorphism (sum_group k (\i. subgroup_generated G (h i)),
                               subgroup_generated G (UNIONS {h i | i IN k}))
                               (group_sum G k)`;;

let SUBGROUP_EPIMORPHISM_ABELIAN_GROUP_SUM = `!k G (h:K->A->bool).
        abelian_group G
        ==> group_epimorphism (sum_group k (\i. subgroup_generated G (h i)),
                               subgroup_generated G (UNIONS {h i | i IN k}))
                               (group_sum G k)`;;

let GROUP_EPIMORPHISM_GROUP_SUM_GEN = `!k l G (h:K->A->bool).
        k SUBSET l
        ==> (group_epimorphism (sum_group l (\i. subgroup_generated G (h i)),G)
                               (group_sum G k) <=>
             pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                                   y IN group_carrier G /\ y IN (h j)
                                   ==> group_mul G x y = group_mul G y x) k /\
             subgroup_generated G (UNIONS {h i | i IN k}) = G)`;;

let GROUP_EPIMORPHISM_GROUP_SUM_EQ = `!k l G (h:K->A->bool).
        k SUBSET l /\
        (!i. i IN k ==> (h i) subgroup_of G)
        ==> (group_epimorphism (sum_group l (\i. subgroup_generated G (h i)),G)
                               (group_sum G k) <=>
             pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                   ==> group_mul G x y = group_mul G y x) k /\
             subgroup_generated G (UNIONS {h i | i IN k}) = G)`;;

let GROUP_EPIMORPHISM_GROUP_SUM = `!k G (h:K->A->bool).
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G
        ==> group_epimorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                              (group_sum G k)`;;

let GROUP_EPIMORPHISM_ABELIAN_GROUP_SUM = `!k G (h:K->A->bool).
        abelian_group G /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G
        ==> group_epimorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                              (group_sum G k)`;;

let GROUP_MONOMORPHISM_GROUP_SUM_GEN = `!k G (h:K->A->bool).
      group_monomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                         (group_sum G k) <=>
      pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                            y IN group_carrier G /\ y IN (h j)
                            ==> group_mul G x y = group_mul G y x) k /\
      !i. i IN k
          ==> group_carrier
                 (subgroup_generated G (h i)) INTER
              group_carrier
                 (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
              {group_id G}`;;

let GROUP_MONOMORPHISM_GROUP_SUM_EQ = `!k G (h:K->A->bool).
      (!i. i IN k ==> (h i) subgroup_of G)
      ==> (group_monomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                              (group_sum G k) <=>
           pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k /\
           !i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})`;;

let GROUP_MONOMORPHISM_GROUP_SUM = `!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of G) /\
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> group_monomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                              (group_sum G k)`;;

let GROUP_MONOMORPHISM_ABELIAN_GROUP_SUM = `!k G (h:K->A->bool).
        abelian_group G /\
        (!i. i IN k ==> (h i) subgroup_of G) /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> group_monomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                               (group_sum G k)`;;

let SUBGROUP_ISOMORPHISM_GROUP_SUM_GEN = `!k G (h:K->A->bool).
        group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),
                           subgroup_generated G (UNIONS {h i | i IN k}))
                          (group_sum G k) <=>
        pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                              y IN group_carrier G /\ y IN (h j)
                              ==> group_mul G x y = group_mul G y x) k /\
        !i. i IN k
          ==> group_carrier
                 (subgroup_generated G (h i)) INTER
              group_carrier
                 (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
              {group_id G}`;;

let SUBGROUP_ISOMORPHISM_GROUP_SUM_EQ = `!k G (h:K->A->bool).
      (!i. i IN k ==> (h i) subgroup_of G)
      ==> (group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),
                              subgroup_generated G (UNIONS {h i | i IN k}))
                             (group_sum G k) <=>
           pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k /\
           !i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})`;;

let SUBGROUP_ISOMORPHISM_GROUP_SUM = `!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of G) /\
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),
                               subgroup_generated G (UNIONS {h i | i IN k}))
                               (group_sum G k)`;;

let SUBGROUP_ISOMORPHISM_ABELIAN_GROUP_SUM = `!k G (h:K->A->bool).
        abelian_group G /\
        (!i. i IN k ==> (h i) subgroup_of G) /\
        (!i. i IN k
             ==> h i INTER
                 group_carrier
                   (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                 {group_id G})
        ==> group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),
                               subgroup_generated G (UNIONS {h i | i IN k}))
                               (group_sum G k)`;;

let GROUP_ISOMORPHISM_GROUP_SUM_GEN = `!k G (h:K->A->bool).
        group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                          (group_sum G k) <=>
        pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                              y IN group_carrier G /\ y IN (h j)
                              ==> group_mul G x y = group_mul G y x) k /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        !i. i IN k
          ==> group_carrier
                 (subgroup_generated G (h i)) INTER
              group_carrier
                 (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
              {group_id G}`;;

let GROUP_ISOMORPHISM_GROUP_SUM_EQ = `!k G (h:K->A->bool).
      (!i. i IN k ==> (h i) subgroup_of G)
      ==> (group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                             (group_sum G k) <=>
           pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k /\
           subgroup_generated G (UNIONS {h i | i IN k}) = G /\
           !i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})`;;

let GROUP_ISOMORPHISM_GROUP_SUM = `!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of G) /\
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                               (group_sum G k)`;;

let GROUP_ISOMORPHISM_ABELIAN_GROUP_SUM = `!k G (h:K->A->bool).
        abelian_group G /\
        (!i. i IN k ==> (h i) subgroup_of G) /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
             ==> h i INTER
                 group_carrier
                   (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                 {group_id G})
        ==> group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                              (group_sum G k)`;;

let ISOMORPHIC_SUM_GROUP_GEN = `!k G (h:K->A->bool).
        pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                              y IN group_carrier G /\ y IN (h j)
                              ==> group_mul G x y = group_mul G y x) k /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
             ==> group_carrier
                    (subgroup_generated G (h i)) INTER
                 group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                 {group_id G})
        ==> sum_group k (\i. subgroup_generated G (h i)) isomorphic_group G`;;

let ISOMORPHIC_SUM_GROUP = `!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of G) /\
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> sum_group k (\i. subgroup_generated G (h i)) isomorphic_group G`;;

let ISOMORPHIC_ABELIAN_SUM_GROUP = `!k G (h:K->A->bool).
        abelian_group G /\
        (!i. i IN k ==> (h i) subgroup_of G) /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> sum_group k (\i. subgroup_generated G (h i)) isomorphic_group G`;;

let ISOMORPHIC_NORMAL_SUM_GROUP = `!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) normal_subgroup_of G) /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> sum_group k (\i. subgroup_generated G (h i)) isomorphic_group G`;;

let CARRIER_SUBGROUP_GENERATED_UNIONS = `!(G:A group) u.
        abelian_group G
        ==> group_carrier(subgroup_generated G (UNIONS u)) =
            IMAGE (group_sum G u)
                  (group_carrier (sum_group u (\i. subgroup_generated G i)))`;;

let CARRIER_SUBGROUP_GENERATED_UNIONS_ALT = `!(G:A group) u.
        abelian_group G
        ==> group_carrier(subgroup_generated G (UNIONS u)) =
            { group_sum G u f | f |
              (!s. s IN u ==> f s IN group_carrier(subgroup_generated G s)) /\
              FINITE {s | s IN u /\ ~(f s = group_id G)}}`;;

let CARRIER_SUBGROUP_GENERATED_UNIONS_FINITE = `!(G:A group) u.
        abelian_group G /\ FINITE u
        ==> group_carrier(subgroup_generated G (UNIONS u)) =
            { group_sum G u f | f |
              (!s. s IN u ==> f s IN group_carrier(subgroup_generated G s))}`;;

let CARRIER_SUBGROUP_GENERATED_UNIONS_EXPLICIT = `!(G:A group) u.
        abelian_group G
        ==> group_carrier(subgroup_generated G (UNIONS u)) =
            { group_sum G t f | t,f |
              FINITE t /\ t SUBSET u /\
              (!s. s IN t ==> f s IN group_carrier(subgroup_generated G s))}`;;

let CARRIER_SUBGROUP_GENERATED_ALT = `!G (s:A->bool).
        abelian_group G /\ s SUBSET group_carrier G
        ==> group_carrier(subgroup_generated G s) =
            { group_sum G s (\x. group_zpow G x (n x)) | n |
              FINITE {x | x IN s /\ ~(n x = &0)}}`;;

let CARRIER_SUBGROUP_GENERATED_FINITE = `!G (s:A->bool).
        abelian_group G /\ FINITE s /\ s SUBSET group_carrier G
        ==> group_carrier(subgroup_generated G s) =
            { group_sum G s (\x. group_zpow G x (n x)) | n IN (:A->int)}`;;

let CARRIER_SUBGROUP_GENERATED_EXPLICIT = `!G (s:A->bool).
        abelian_group G /\ s SUBSET group_carrier G
        ==> group_carrier(subgroup_generated G s) =
            { group_sum G t (\x. group_zpow G x (n x)) | t,n |
              FINITE t /\ t SUBSET s}`;;

(* ------------------------------------------------------------------------- *)
(* Structure theorems for periodic Abelian groups in terms of p-groups.      *)
(* ------------------------------------------------------------------------- *)

let SUBGROUP_GENERATED_UNIONS_PRIME_TORSION_FINITE = `!(G:A group) P.
      FINITE {p | prime p /\ P p}
      ==> subgroup_generated G
           (UNIONS
            {{ x | x IN group_carrier G /\
                   ?k. group_element_order G x = p EXP k} | prime p /\ P p}) =
          subgroup_generated G
           {x | x IN group_carrier G /\
                !p. prime p /\ p divides group_element_order G x ==> P p}`;;

let SUBGROUP_GENERATED_UNIONS_PRIME_TORSION = `!(G:A group) P.
        subgroup_generated G
         (UNIONS
           {{ x | x IN group_carrier G /\
                  ?k. group_element_order G x = p EXP k} | prime p /\ P p}) =
        subgroup_generated G
         {x | x IN group_carrier G /\ ~(group_element_order G x = 0) /\
              !p. prime p /\ p divides group_element_order G x ==> P p}`;;

let SUBGROUP_GENERATED_UNIONS_PRIME_TORSION_FULL = `!(G:A group).
        subgroup_generated G
         (UNIONS
           {{ x | x IN group_carrier G /\
                  ?k. group_element_order G x = p EXP k} | prime p}) =
        subgroup_generated G
         {x | x IN group_carrier G /\ ~(group_element_order G x = 0)}`;;

let PGROUP_PRIME_TORSION = `!(G:A group) p.
        abelian_group G /\ prime p
        ==> pgroup {p} (subgroup_generated G
                         {x | x IN group_carrier G /\
                              ?k. group_element_order G x = p EXP k})`;;

let PGROUP_SUBSET_PRIME_TORSION = `!(G:A group) p s.
        prime p /\
        s SUBSET group_carrier G /\
        pgroup {p} (subgroup_generated G s)
        ==> s SUBSET {x | x IN group_carrier G /\
                          ?k. group_element_order G x = p EXP k}`;;

let ABELIAN_GROUP_TORSION_ISOMORPHISM = `!G:A group.
        abelian_group G
        ==> group_isomorphism
             (sum_group {p | prime p}
               (\p. subgroup_generated G
                     {x | x IN group_carrier G /\
                          ?k. group_element_order G x = p EXP k}),
              subgroup_generated G
               {x | x IN group_carrier G /\ ~(group_element_order G x = 0)})
             (group_sum G {p | prime p})`;;

let ABELIAN_GROUP_TORSION_STRUCTURE = `!G:A group.
        abelian_group G
        ==> subgroup_generated G
               {x | x IN group_carrier G /\ ~(group_element_order G x = 0)}
            isomorphic_group
            sum_group {p | prime p}
              (\p. subgroup_generated G
                     {x | x IN group_carrier G /\
                          ?k. group_element_order G x = p EXP k})`;;

let TORSION_ABELIAN_GROUP_ISOMORPHISM = `!G:A group.
        abelian_group G /\
        (!x. x IN group_carrier G ==> ~(group_element_order G x = 0))
        ==> group_isomorphism
             (sum_group {p | prime p}
               (\p. subgroup_generated G
                     {x | x IN group_carrier G /\
                          ?k. group_element_order G x = p EXP k}),
              G)
             (group_sum G {p | prime p})`;;

let TORSION_ABELIAN_GROUP_STRUCTURE = `!G:A group.
        abelian_group G /\
        (!x. x IN group_carrier G ==> ~(group_element_order G x = 0))
        ==> G isomorphic_group
            sum_group {p | prime p}
              (\p. subgroup_generated G
                     {x | x IN group_carrier G /\
                          ?k. group_element_order G x = p EXP k})`;;

let FINITE_ABELIAN_GROUP_STRUCTURE = `!G:A group.
        abelian_group G /\ FINITE(group_carrier G)
        ==> G isomorphic_group
            sum_group {p | prime p /\ p divides CARD(group_carrier G)}
              (\p. subgroup_generated G
                     {x | x IN group_carrier G /\
                          ?k. group_element_order G x = p EXP k})`;;

let FINITE_ABELIAN_GROUP_STRUCTURE_ALT = `!G:A group.
        abelian_group G /\ FINITE(group_carrier G)
        ==> G isomorphic_group
            product_group {p | prime p /\ p divides CARD(group_carrier G)}
              (\p. subgroup_generated G
                     {x | x IN group_carrier G /\
                          ?k. group_element_order G x = p EXP k})`;;

let TORSION_ABELIAN_GROUP_AS_SUM_OF_PGROUPS = `!G:A group.
        abelian_group G
        ==> ((!x. x IN group_carrier G ==> ~(group_element_order G x = 0)) <=>
             ?H:num->A group.
                (!p. prime p ==> pgroup {p} (H p)) /\
                G isomorphic_group sum_group {p | prime p} H)`;;

(* ------------------------------------------------------------------------- *)
(* Structure theorem for finitely generated Abelian groups.                  *)
(* ------------------------------------------------------------------------- *)

let FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM = `!G (s:A->bool).
        abelian_group G /\ FINITE s
        ==> ?t. FINITE t /\ CARD t <= CARD s /\ t SUBSET group_carrier G /\
                subgroup_generated G t = subgroup_generated G s /\
                group_isomorphism
                  (sum_group t (\x. subgroup_generated G {x}),
                   subgroup_generated G s)
                  (group_sum G t)`;;

let FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM_ALT = `!G (s:A->bool).
        abelian_group G /\ FINITE s
        ==> ?t. FINITE t /\ CARD t <= CARD s /\ t SUBSET group_carrier G /\
                subgroup_generated G t = subgroup_generated G s /\
                group_isomorphism
                  (product_group t (\x. subgroup_generated G {x}),
                   subgroup_generated G s)
                  (group_sum G t)`;;

let FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_EXPLICIT = `!G (s:A->bool).
        abelian_group G /\ FINITE s
        ==> ?t. FINITE t /\ CARD t <= CARD s /\ t SUBSET group_carrier G /\
                subgroup_generated G t = subgroup_generated G s /\
                subgroup_generated G s isomorphic_group
                sum_group t (\x. subgroup_generated G {x})`;;

let FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_EXPLICIT_ALT = `!G (s:A->bool).
        abelian_group G /\ FINITE s
        ==> ?t. FINITE t /\ CARD t <= CARD s /\ t SUBSET group_carrier G /\
                subgroup_generated G t = subgroup_generated G s /\
                subgroup_generated G s isomorphic_group
                product_group t (\x. subgroup_generated G {x})`;;

let FINITELY_GENERATED_ABELIAN_GROUP_STRUCTURE_EXPLICIT = `!G:A group.
        finitely_generated_group G /\ abelian_group G <=>
        ?t. FINITE t /\ t SUBSET group_carrier G /\
            G isomorphic_group sum_group t (\x. subgroup_generated G {x})`;;

let FINITELY_GENERATED_ABELIAN_GROUP_STRUCTURE_EXPLICIT_ALT = `!G:A group.
        finitely_generated_group G /\ abelian_group G <=>
        ?t. FINITE t /\ t SUBSET group_carrier G /\
            G isomorphic_group product_group t (\x. subgroup_generated G {x})`;;

let FINITELY_GENERATED_ABELIAN_GROUP_AS_SUM_OF_CYCLIC_GROUPS = `!G:A group.
        finitely_generated_group G /\ abelian_group G <=>
        ?n H:num->A group.
            (!i. 1 <= i /\ i <= n ==> cyclic_group (H i)) /\
            G isomorphic_group sum_group (1..n) H`;;

let FINITELY_GENERATED_ABELIAN_GROUP_AS_PRODUCT_OF_CYCLIC_GROUPS = `!G:A group.
        finitely_generated_group G /\ abelian_group G <=>
        ?n H:num->A group.
            (!i. 1 <= i /\ i <= n ==> cyclic_group (H i)) /\
            G isomorphic_group product_group (1..n) H`;;

let FINITELY_GENERATED_ABELIAN_GROUP_AS_SUM_OF_INTEGER_MOD_GROUPS = `!G:A group.
      finitely_generated_group G /\ abelian_group G <=>
      ?n d. G isomorphic_group sum_group (1..n) (\i. integer_mod_group(d i))`;;

let FINITELY_GENERATED_ABELIAN_GROUP_AS_PRODUCT_OF_INTEGER_MOD_GROUPS = `!G:A group.
      finitely_generated_group G /\ abelian_group G <=>
      ?n d. G isomorphic_group
            product_group (1..n) (\i. integer_mod_group(d i))`;;

let FINITELY_GENERATED_ABELIAN_GROUP_AS_SUM_OF_INTEGER_GROUPS = `!G:A group.
      finitely_generated_group G /\ abelian_group G /\
      (!x. x IN group_carrier G ==> group_element_order G x <= 1) <=>
      ?n. G isomorphic_group sum_group (1..n) (\i. integer_group)`;;

let FINITELY_GENERATED_ABELIAN_GROUP_AS_PRODUCT_OF_INTEGER_GROUPS = `!G:A group.
      finitely_generated_group G /\ abelian_group G /\
      (!x. x IN group_carrier G ==> group_element_order G x <= 1) <=>
      ?n. G isomorphic_group product_group (1..n) (\i. integer_group)`;;

(* ------------------------------------------------------------------------- *)
(* Free Abelian groups on a set, using the "frag" type constructor.          *)
(* ------------------------------------------------------------------------- *)

let free_abelian_group = new_definition
 `free_abelian_group (s:A->bool) =
    group({c | frag_support c SUBSET s},frag_0,frag_neg,frag_add)`;;

let FREE_ABELIAN_GROUP = `(!s:A->bool.
        group_carrier(free_abelian_group s) = {c | frag_support c SUBSET s}) /\
   (!s:A->bool. group_id(free_abelian_group s) = frag_0) /\
   (!s:A->bool. group_inv(free_abelian_group s) = frag_neg) /\
   (!s:A->bool. group_mul(free_abelian_group s) = frag_add)`;;

let ABELIAN_FREE_ABELIAN_GROUP = `!s:A->bool. abelian_group(free_abelian_group s)`;;

let FREE_ABELIAN_GROUP_POW = `!(s:A->bool) x n.
        group_pow (free_abelian_group s) x n = frag_cmul (&n) x`;;

let FREE_ABELIAN_GROUP_ZPOW = `!(s:A->bool) x n.
        group_zpow (free_abelian_group s) x n = frag_cmul n x`;;

let FRAG_OF_IN_FREE_ABELIAN_GROUP = `!s x:A. frag_of x IN group_carrier(free_abelian_group s) <=> x IN s`;;

let FREE_ABELIAN_GROUP_INDUCT = `!P s:A->bool.
        P(frag_0) /\
        (!x y. x IN group_carrier(free_abelian_group s) /\
               y IN group_carrier(free_abelian_group s) /\
               P x /\ P y
               ==> P(frag_sub x y)) /\
        (!a. a IN s ==> P(frag_of a))
        ==> !x. x IN group_carrier(free_abelian_group s) ==> P x`;;

let FREE_ABELIAN_GROUP_UNIVERSAL = `!(f:A->B) s G.
        IMAGE f s SUBSET group_carrier G /\ abelian_group G
        ==> ?h. group_homomorphism(free_abelian_group s,G) h /\
                !x. x IN s ==> h(frag_of x) = f x`;;

let ISOMORPHIC_GROUP_INTEGER_FREE_ABELIAN_GROUP_SING = `!x:A. integer_group isomorphic_group free_abelian_group {x}`;;

let GROUP_HOMOMORPHISM_FREE_ABELIAN_GROUPS_ID = `!k k':A->bool.
    group_homomorphism (free_abelian_group k,free_abelian_group k') (\x. x) <=>
    k SUBSET k'`;;

let GROUP_ISOMORPHISM_FREE_ABELIAN_GROUP_SUM = `!k (f:K->A->bool).
        pairwise (\i j. DISJOINT (f i) (f j)) k
        ==> group_isomorphism (sum_group k (\i. free_abelian_group(f i)),
                               free_abelian_group(UNIONS {f i | i IN k}))
                              (iterate frag_add k)`;;

let ISOMORPHIC_FREE_ABELIAN_GROUP_UNIONS = `!k:(A->bool)->bool.
        pairwise DISJOINT k
        ==> free_abelian_group(UNIONS k) isomorphic_group
            sum_group k free_abelian_group`;;

let ISOMORPHIC_SUM_INTEGER_GROUP = `!k:A->bool.
        sum_group k (\i. integer_group) isomorphic_group free_abelian_group k`;;

let CARD_EQ_FREE_ABELIAN_GROUP_INFINITE = `!s:A->bool. INFINITE s ==> group_carrier(free_abelian_group s) =_c s`;;

let CARD_EQ_HOMOMORPHISMS_FROM_FREE_ABELIAN_GROUP = `!(s:A->bool) (G:B group).
        abelian_group G
        ==> {f | EXTENSIONAL (group_carrier(free_abelian_group s)) f /\
                 group_homomorphism(free_abelian_group s,G) f} =_c
            (group_carrier G) ^_c s`;;

let ISOMORPHIC_FREE_ABELIAN_GROUPS = `!(s:A->bool) (t:B->bool).
      free_abelian_group s isomorphic_group free_abelian_group t <=>
      s =_c t`;;

(* ------------------------------------------------------------------------- *)
(* Basic things about exact sequences.                                       *)
(* ------------------------------------------------------------------------- *)

let group_exactness = new_definition
 `group_exactness (G,H,K) ((f:A->B),(g:B->C)) <=>
        group_homomorphism (G,H) f /\ group_homomorphism (H,K) g /\
        group_image (G,H) f = group_kernel (H,K) g`;;

let short_exact_sequence = new_definition
 `short_exact_sequence(A,B,C) (f:A->B,g:B->C) <=>
        group_monomorphism (A,B) f /\
        group_exactness (A,B,C) (f,g) /\
        group_epimorphism (B,C) g`;;

let SHORT_EXACT_SEQUENCE = `!(f:A->B) (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g) <=>
        group_monomorphism (A,B) f /\
        group_epimorphism (B,C) g /\
        group_image (A,B) f = group_kernel (B,C) g`;;

let GROUP_EXACTNESS_MONOMORPHISM = `!f:(A->B) (g:B->C) A B C.
        trivial_group A
        ==> (group_exactness (A,B,C) (f,g) <=>
             group_homomorphism(A,B) f /\ group_monomorphism (B,C) g)`;;

let GROUP_EXACTNESS_EPIMORPHISM = `!f:(A->B) (g:B->C) A B C.
        trivial_group C
        ==> (group_exactness (A,B,C) (f,g) <=>
             group_epimorphism(A,B) f /\ group_homomorphism (B,C) g)`;;

let EXTREMELY_SHORT_EXACT_SEQUENCE = `!f:(A->B) (g:B->C) A B C.
        group_exactness (A,B,C) (f,g) /\
        trivial_group A /\ trivial_group C
        ==> trivial_group B`;;

let GROUP_EXACTNESS_EPIMORPHISM_EQ_TRIVIALITY = `!(f:A->B) (g:B->C) (h:C->D) A B C D.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h)
        ==> (group_epimorphism (A,B) f <=> trivial_homomorphism(B,C) g)`;;

let GROUP_EXACTNESS_MONOMORPHISM_EQ_TRIVIALITY = `!(f:A->B) (g:B->C) (h:C->D) A B C D.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h)
        ==> (group_monomorphism (C,D) h <=>  trivial_homomorphism(B,C) g)`;;

let VERY_SHORT_EXACT_SEQUENCE = `!(f:A->B) (g:B->C) (h:C->D) A B C D.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h) /\
        trivial_group A /\ trivial_group D
        ==> group_isomorphism (B,C) g`;;

let GROUP_EXACTNESS_EQ_TRIVIALITY = `!f:(A->B) (g:B->C) (h:C->D) (k:D->E) A B C D E.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h) /\
        group_exactness (C,D,E) (h,k)
        ==> (trivial_group C <=>
             group_epimorphism (A,B) f /\
             group_monomorphism (D,E) k)`;;

let GROUP_EXACTNESS_IMP_TRIVIALITY = `!(f:A->B) (g:B->C) (h:C->D) (k:D->E) A B C D E.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h) /\
        group_exactness (C,D,E) (h,k) /\
        group_isomorphism (A,B) f /\
        group_isomorphism (D,E) k
        ==> trivial_group C`;;

let GROUP_EXACTNESS_ISOMORPHISM_EQ_TRIVIALITY = `!(f:A->B) (g:B->C) (h:C->D) (j:D->E) (k:E->G) A B C D E G.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h) /\
        group_exactness (C,D,E) (h,j) /\
        group_exactness (D,E,G) (j,k)
        ==> (group_isomorphism (C,D) h <=>
             trivial_homomorphism(B,C) g /\ trivial_homomorphism(D,E) j)`;;

let GROUP_EXACTNESS_ISOMORPHISM_EQ_MONO_EPI = `!(f:A->B) (g:B->C) (h:C->D) (j:D->E) (k:E->G) A B C D E G.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h) /\
        group_exactness (C,D,E) (h,j) /\
        group_exactness (D,E,G) (j,k)
        ==> (group_isomorphism (C,D) h <=>
             group_epimorphism(A,B) f /\ group_monomorphism(E,G) k)`;;

let SHORT_EXACT_SEQUENCE_NORMAL_SUBGROUP = `!G n:A->bool.
        n normal_subgroup_of G
        ==> short_exact_sequence
             (subgroup_generated G n,G,quotient_group G n)
             ((\x. x),right_coset G n)`;;

let SHORT_EXACT_SEQUENCE_PROD_GROUP = `!(G:A group) (H:B group).
        short_exact_sequence(G,prod_group G H,H) ((\x. x,group_id H),SND)`;;

let SHORT_EXACT_SEQUENCE_PROD_GROUP_ALT = `!(G:A group) (H:B group).
        short_exact_sequence(H,prod_group G H,G) ((\x. group_id G,x),FST)`;;

let EXACT_SEQUENCE_SUM_LEMMA = `!(f:X->C) (g:X->D) (h:A->C) (i:A->X) (j:B->X) (k:B->D) A B C D X.
        abelian_group X /\
        group_isomorphism(A,C) h /\
        group_isomorphism(B,D) k /\
        group_exactness(A,X,D) (i,g) /\
        group_exactness(B,X,C) (j,f) /\
        (!x. x IN group_carrier A ==> f(i x) = h x) /\
        (!x. x IN group_carrier B ==> g(j x) = k x)
        ==> group_isomorphism (prod_group A B,X)
                              (\(x,y). group_mul X (i x) (j y)) /\
            group_isomorphism (X,prod_group C D) (\z. f z,g z)`;;

let SHORT_EXACT_SEQUENCE_QUOTIENT = `!(f:A->B) (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g)
        ==> subgroup_generated B (group_image(A,B) f) isomorphic_group A /\
            quotient_group B (group_image(A,B) f) isomorphic_group C`;;

let TRIVIAL_GROUPS_IMP_SHORT_EXACT_SEQUENCE = `!(f:A->B) (g:B->C) (h:C->D) (k:D->E) A B C D E.
        trivial_group A /\ trivial_group E /\
        group_exactness(A,B,C) (f,g) /\
        group_exactness(B,C,D) (g,h) /\
        group_exactness(C,D,E) (h,k)
        ==> short_exact_sequence(B,C,D) (g,h)`;;

let SHORT_EXACT_SEQUENCE_TRIVIAL_GROUPS = `!(g:B->C) h B C D.
        short_exact_sequence(B,C,D) (g,h) <=>
        ?f:(A->B) (k:D->E) A E.
                trivial_group A /\ trivial_group E /\
                group_exactness(A,B,C) (f,g) /\
                group_exactness(B,C,D) (g,h) /\
                group_exactness(C,D,E) (h,k)`;;

let SPLITTING_SUBLEMMA_GEN = `!(f:A->B) (g:B->C) A B C h k.
        group_exactness(A,B,C) (f,g) /\
        group_image(A,B) f = h /\ k subgroup_of B /\
        h INTER k SUBSET {group_id B} /\ group_setmul B h k = group_carrier B
        ==> group_isomorphism(subgroup_generated B k,
                              subgroup_generated C (group_image(B,C) g)) g`;;

let SPLITTING_SUBLEMMA = `!(f:A->B) (g:B->C) A B C h k.
        short_exact_sequence(A,B,C) (f,g) /\
        group_image(A,B) f = h /\ k subgroup_of B /\
        h INTER k SUBSET {group_id B} /\ group_setmul B h k = group_carrier B
        ==> group_isomorphism(A,subgroup_generated B h) f /\
            group_isomorphism(subgroup_generated B k,C) g`;;

let SPLITTING_LEMMA_LEFT_GEN = `!(f:A->B) f' (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        group_homomorphism(B,A) f' /\
        group_isomorphism(A,A) (f' o f)
        ==> ?h k. h normal_subgroup_of B /\ k normal_subgroup_of B /\
                  h INTER k SUBSET {group_id B} /\
                  group_setmul B h k = group_carrier B /\
                  group_isomorphism(A,subgroup_generated B h) f /\
                  group_isomorphism(subgroup_generated B k,C) g`;;

let SPLITTING_LEMMA_LEFT = `!(f:A->B) f' (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        group_homomorphism(B,A) f' /\
        (!x. x IN group_carrier A ==> f'(f x) = x)
        ==> ?h k. h normal_subgroup_of B /\ k normal_subgroup_of B /\
                  h INTER k SUBSET {group_id B} /\
                  group_setmul B h k = group_carrier B /\
                  group_isomorphism(A,subgroup_generated B h) f /\
                  group_isomorphism(subgroup_generated B k,C) g`;;

let SPLITTING_LEMMA_LEFT_PROD_GROUP = `!(f:A->B) f' (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        abelian_group B /\
        group_homomorphism(B,A) f' /\
        (!x. x IN group_carrier A ==> f'(f x) = x)
        ==> B isomorphic_group prod_group A C`;;

let SPLITTING_LEMMA_RIGHT_GEN = `!(f:A->B) (g:B->C) g' A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        group_homomorphism(C,B) g' /\
        group_isomorphism(C,C) (g o g')
        ==> ?h k. h normal_subgroup_of B /\ k subgroup_of B /\
                  h INTER k SUBSET {group_id B} /\
                  group_setmul B h k = group_carrier B /\
                  group_isomorphism(A,subgroup_generated B h) f /\
                  group_isomorphism(subgroup_generated B k,C) g`;;

let SPLITTING_LEMMA_RIGHT = `!(f:A->B) (g:B->C) g' A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        group_homomorphism(C,B) g' /\
        (!z. z IN group_carrier C ==> g(g' z) = z)
        ==> ?h k. h normal_subgroup_of B /\ k subgroup_of B /\
                  h INTER k SUBSET {group_id B} /\
                  group_setmul B h k = group_carrier B /\
                  group_isomorphism(A,subgroup_generated B h) f /\
                  group_isomorphism(subgroup_generated B k,C) g`;;

let SPLITTING_LEMMA_RIGHT_PROD_GROUP = `!(f:A->B) (g:B->C) g' A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        abelian_group B /\
        group_homomorphism(C,B) g' /\
        (!z. z IN group_carrier C ==> g(g' z) = z)
        ==> B isomorphic_group prod_group A C`;;

let SPLITTING_LEMMA_FREE_ABELIAN_GROUP = `!(f:A->B) (g:B->C) A B C (s:D->bool).
        short_exact_sequence (A,B,C) (f,g) /\
        abelian_group B /\ C isomorphic_group free_abelian_group s
        ==> B isomorphic_group prod_group A C`;;

let FOUR_LEMMA_MONO = `!(f:A->B) (g:B->C) (h:C->D) (f':A'->B') (g':B'->C') (h':C'->D') a b c d
     A B C D A' B' C' D'.
      group_epimorphism(A,A') a /\
      group_monomorphism(B,B') b /\
      group_homomorphism(C,C') c /\
      group_monomorphism(D,D') d /\
      group_exactness(A,B,C) (f,g) /\ group_exactness(B,C,D) (g,h) /\
      group_exactness(A',B',C') (f',g') /\ group_exactness(B',C',D') (g',h') /\
      (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
      (!y. y IN group_carrier B ==> g'(b y) = c(g y)) /\
      (!z. z IN group_carrier C ==> h'(c z) = d(h z))
      ==> group_monomorphism(C,C') c`;;

let FOUR_LEMMA_EPI = `!(f:A->B) (g:B->C) (h:C->D) (f':A'->B') (g':B'->C') (h':C'->D') a b c d
     A B C D A' B' C' D'.
      group_epimorphism(A,A') a /\
      group_homomorphism(B,B') b /\
      group_epimorphism(C,C') c /\
      group_monomorphism(D,D') d /\
      group_exactness(A,B,C) (f,g) /\ group_exactness(B,C,D) (g,h) /\
      group_exactness(A',B',C') (f',g') /\ group_exactness(B',C',D') (g',h') /\
      (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
      (!y. y IN group_carrier B ==> g'(b y) = c(g y)) /\
      (!z. z IN group_carrier C ==> h'(c z) = d(h z))
      ==> group_epimorphism(B,B') b`;;

let FIVE_LEMMA = `!(f:A->B) (g:B->C) (h:C->D) (k:D->E)
    (f':A'->B') (g':B'->C') (h':C'->D') (k':D'->E') a b c d e
     A B C D E A' B' C' D' E'.
      group_epimorphism(A,A') a /\
      group_isomorphism(B,B') b /\
      group_homomorphism(C,C') c /\
      group_isomorphism(D,D') d /\
      group_monomorphism(E,E') e /\
      group_exactness(A,B,C) (f,g) /\
      group_exactness(B,C,D) (g,h) /\
      group_exactness(C,D,E) (h,k) /\
      group_exactness(A',B',C') (f',g') /\
      group_exactness(B',C',D') (g',h') /\
      group_exactness(C',D',E') (h',k') /\
      (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
      (!y. y IN group_carrier B ==> g'(b y) = c(g y)) /\
      (!z. z IN group_carrier C ==> h'(c z) = d(h z)) /\
      (!w. w IN group_carrier D ==> k'(d w) = e(k w))
      ==> group_isomorphism(C,C') c`;;

let SHORT_FIVE_LEMMA_MONO = `!(f:A->B) (g:B->C) (f':A'->B') (g':B'->C') a b c A B C A' B' C'.
        group_monomorphism(A,A') a /\
        group_homomorphism(B,B') b /\
        group_monomorphism(C,C') c /\
        short_exact_sequence(A,B,C) (f,g) /\
        short_exact_sequence(A',B',C') (f',g') /\
        (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
        (!y. y IN group_carrier B ==> g'(b y) = c(g y))
        ==> group_monomorphism(B,B') b`;;

let SHORT_FIVE_LEMMA_EPI = `!(f:A->B) (g:B->C) (f':A'->B') (g':B'->C') a b c A B C A' B' C'.
        group_epimorphism(A,A') a /\
        group_homomorphism(B,B') b /\
        group_epimorphism(C,C') c /\
        short_exact_sequence(A,B,C) (f,g) /\
        short_exact_sequence(A',B',C') (f',g') /\
        (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
        (!y. y IN group_carrier B ==> g'(b y) = c(g y))
        ==> group_epimorphism(B,B') b`;;

let SHORT_FIVE_LEMMA = `!(f:A->B) (g:B->C) (f':A'->B') (g':B'->C') a b c A B C A' B' C'.
        group_isomorphism(A,A') a /\
        group_homomorphism(B,B') b /\
        group_isomorphism(C,C') c /\
        short_exact_sequence(A,B,C) (f,g) /\
        short_exact_sequence(A',B',C') (f',g') /\
        (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
        (!y. y IN group_carrier B ==> g'(b y) = c(g y))
        ==> group_isomorphism(B,B') b`;;

let EXACT_SEQUENCE_HEXAGON_LEMMA = `!(f:X->C) (g:X->D) (h:A->C) (h':C->A) (i:A->X) (j:B->X) (k:B->D) (k':D->B)
    (a:A->Y) (b:B->Y) (c:W->C) (d:W->D) (l:W->X) (m:X->Y) A B C D W X Y.
        abelian_group X /\
        group_homomorphism(A,Y) a /\
        group_homomorphism(B,Y) b /\
        group_homomorphism(W,C) c /\
        group_homomorphism(W,D) d /\
        group_isomorphisms(A,C) (h,h') /\
        group_isomorphisms(B,D) (k,k') /\
        group_exactness(A,X,D) (i,g) /\
        group_exactness(B,X,C) (j,f) /\
        group_exactness(W,X,Y) (l,m) /\
        (!x. x IN group_carrier W ==> f(l x) = c x) /\
        (!x. x IN group_carrier W ==> g(l x) = d x) /\
        (!x. x IN group_carrier A ==> f(i x) = h x) /\
        (!x. x IN group_carrier A ==> m(i x) = a x) /\
        (!x. x IN group_carrier B ==> g(j x) = k x) /\
        (!x. x IN group_carrier B ==> m(j x) = b x)
        ==> !x. x IN group_carrier W
                ==> group_inv Y (a(h'(c x))) = b(k'(d x))`;;
