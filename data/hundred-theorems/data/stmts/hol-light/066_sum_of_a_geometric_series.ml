(* ========================================================================= *)
(* Elementary real analysis, with some supporting HOL88 compatibility stuff. *)
(* ========================================================================= *)

let dest_neg_imp tm =
  try dest_imp tm with Failure _ ->
  try (dest_neg tm,mk_const("F",[]))
  with Failure _ -> failwith "dest_neg_imp";;

(* ------------------------------------------------------------------------- *)
(* The quantifier movement conversions.                                      *)
(* ------------------------------------------------------------------------- *)

let (CONV_OF_RCONV: conv -> conv) =
  let rec get_bv tm =
    if is_abs tm then bndvar tm
    else if is_comb tm then try get_bv (rand tm)
            with Failure _ -> get_bv (rator tm)
    else failwith "" in
  fun conv tm ->
  let v = get_bv tm in
  let th1 = conv tm in
  let th2 = ONCE_DEPTH_CONV (GEN_ALPHA_CONV v) (rhs(concl th1)) in
  TRANS th1 th2;;

let (CONV_OF_THM: thm -> conv) =
  CONV_OF_RCONV o REWR_CONV;;

let (X_FUN_EQ_CONV:term->conv) =
  fun v -> (REWR_CONV FUN_EQ_THM) THENC GEN_ALPHA_CONV v;;

let (FUN_EQ_CONV:conv) =
  fun tm ->
    let vars = frees tm in
    let op,[ty1;ty2] = dest_type(type_of (lhs tm)) in
    if op = "fun"
       then let varnm =
                if (is_vartype ty1) then "x" else
                   hd(explode(fst(dest_type ty1))) in
            let x = variant vars (mk_var(varnm,ty1)) in
            X_FUN_EQ_CONV x tm
       else failwith "FUN_EQ_CONV";;

let (SINGLE_DEPTH_CONV:conv->conv) =
  let rec SINGLE_DEPTH_CONV conv tm =
    try conv tm with Failure _ ->
    (SUB_CONV (SINGLE_DEPTH_CONV conv) THENC (TRY_CONV conv)) tm in
  SINGLE_DEPTH_CONV;;

let (OLD_SKOLEM_CONV:conv) =
  SINGLE_DEPTH_CONV (REWR_CONV SKOLEM_THM);;

let (X_SKOLEM_CONV:term->conv) =
  fun v -> OLD_SKOLEM_CONV THENC GEN_ALPHA_CONV v;;

let EXISTS_UNIQUE_CONV tm =
  let v = bndvar(rand tm) in
  let th1 = REWR_CONV EXISTS_UNIQUE_THM tm in
  let tm1 = rhs(concl th1) in
  let vars = frees tm1 in
  let v = variant vars v in
  let v' = variant (v::vars) v in
  let th2 =
   (LAND_CONV(GEN_ALPHA_CONV v) THENC
    RAND_CONV(BINDER_CONV(GEN_ALPHA_CONV v') THENC
              GEN_ALPHA_CONV v)) tm1 in
  TRANS th1 th2;;

let NOT_FORALL_CONV = CONV_OF_THM NOT_FORALL_THM;;

let NOT_EXISTS_CONV = CONV_OF_THM NOT_EXISTS_THM;;

let RIGHT_IMP_EXISTS_CONV = CONV_OF_THM RIGHT_IMP_EXISTS_THM;;

let FORALL_IMP_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_FORALL_IMP_THM ORELSEC
   REWR_CONV RIGHT_FORALL_IMP_THM ORELSEC
   REWR_CONV LEFT_FORALL_IMP_THM);;

let EXISTS_AND_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_EXISTS_AND_THM ORELSEC
   REWR_CONV LEFT_EXISTS_AND_THM ORELSEC
   REWR_CONV RIGHT_EXISTS_AND_THM);;

let LEFT_IMP_EXISTS_CONV = CONV_OF_THM LEFT_IMP_EXISTS_THM;;

let LEFT_AND_EXISTS_CONV tm =
  let v = bndvar(rand(rand(rator tm))) in
  (REWR_CONV LEFT_AND_EXISTS_THM THENC TRY_CONV (GEN_ALPHA_CONV v)) tm;;

let RIGHT_AND_EXISTS_CONV =
  CONV_OF_THM RIGHT_AND_EXISTS_THM;;

let AND_FORALL_CONV = CONV_OF_THM AND_FORALL_THM;;

(* ------------------------------------------------------------------------- *)
(* The slew of named tautologies.                                            *)
(* ------------------------------------------------------------------------- *)

let F_IMP = TAUT `!t. ~t ==> t ==> F`;;

let LEFT_AND_OVER_OR = TAUT
  `!t1 t2 t3. t1 /\ (t2 \/ t3) <=> t1 /\ t2 \/ t1 /\ t3`;;

let RIGHT_AND_OVER_OR = TAUT
  `!t1 t2 t3. (t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1`;;

(* ------------------------------------------------------------------------- *)
(* Something trivial and useless.                                            *)
(* ------------------------------------------------------------------------- *)

let INST_TY_TERM(substl,insttyl) th = INST substl (INST_TYPE insttyl th);;

(* ------------------------------------------------------------------------- *)
(* Derived rules.                                                            *)
(* ------------------------------------------------------------------------- *)

let NOT_MP thi th =
  try MP thi th with Failure _ ->
  try let t = dest_neg (concl thi) in
      MP(MP (SPEC t F_IMP) thi) th
  with Failure _ -> failwith "NOT_MP";;

(* ------------------------------------------------------------------------- *)
(* Creating half abstractions.                                               *)
(* ------------------------------------------------------------------------- *)

let MK_ABS qth =
  try let ov = bndvar(rand(concl qth)) in
      let bv,rth = SPEC_VAR qth in
      let sth = ABS bv rth in
      let cnv = ALPHA_CONV ov in
      CONV_RULE(BINOP_CONV cnv) sth
  with Failure _ -> failwith "MK_ABS";;

let HALF_MK_ABS th =
  try let th1 = MK_ABS th in
      CONV_RULE(LAND_CONV ETA_CONV) th1
  with Failure _ -> failwith "HALF_MK_ABS";;

(* ------------------------------------------------------------------------- *)
(* Old substitution primitive, now a (not very efficient) derived rule.      *)
(* ------------------------------------------------------------------------- *)

let SUBST thl pat th =
  let eqs,vs = unzip thl in
  let gvs = map (genvar o type_of) vs in
  let gpat = subst (zip gvs vs) pat in
  let ls,rs = unzip (map (dest_eq o concl) eqs) in
  let ths = map (ASSUME o mk_eq) (zip gvs rs) in
  let th1 = ASSUME gpat in
  let th2 = SUBS ths th1 in
  let th3 = itlist DISCH (map concl ths) (DISCH gpat th2) in
  let th4 = INST (zip ls gvs) th3 in
  MP (rev_itlist (C MP) eqs th4) th;;

(* ------------------------------------------------------------------------- *)
(* Various theorems have different names.                                    *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;

let LESS_EQUAL_ANTISYM = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_ANTISYM)));;
let NOT_LESS_0 = GEN_ALL(EQF_ELIM(SPEC_ALL(CONJUNCT1 LT)));;
let LESS_LEMMA1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL(CONJUNCT2 LT))));;
let LESS_SUC_REFL = ARITH_RULE `!n. n < SUC n`;;
let LESS_EQ_SUC_REFL = ARITH_RULE `!n. n <= SUC n`;;
let LESS_EQUAL_ADD = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_EXISTS)));;
let LESS_EQ_IMP_LESS_SUC = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_SUC_LE)));;
let LESS_MONO_ADD = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_ADD_RCANCEL)));;
let LESS_SUC = ARITH_RULE `!m n. m < n ==> m < (SUC n)`;;
let LESS_ADD_1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL
  (REWRITE_RULE[ADD1] LT_EXISTS))));;
let SUC_SUB1 = ARITH_RULE `!m. SUC m - 1 = m`;;
let LESS_ADD_SUC = ARITH_RULE `!m n. m < m + SUC n`;;
let OR_LESS = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_SUC_LT)));;
let NOT_SUC_LESS_EQ = ARITH_RULE `!n m. ~(SUC n <= m) <=> m <= n`;;
let LESS_LESS_CASES = ARITH_RULE `!m n. (m = n) \/ m < n \/ n < m`;;
let SUB_SUB = `!b c. c <= b ==> (!a. a - (b - c) = (a + c) - b)`;;
let LESS_CASES_IMP = ARITH_RULE `!m n. ~(m < n) /\ ~(m = n) ==> n < m`;;
let SUB_LESS_EQ = ARITH_RULE `!n m. (n - m) <= n`;;
let SUB_EQ_EQ_0 = ARITH_RULE `!m n. (m - n = m) <=> (m = 0) \/ (n = 0)`;;
let SUB_LEFT_LESS_EQ =
  ARITH_RULE `!m n p. m <= (n - p) <=> (m + p) <= n \/ m <= 0`;;
let SUB_LEFT_GREATER_EQ = ARITH_RULE `!m n p. m >= (n - p) <=> (m + p) >= n`;;
let LESS_0_CASES = ARITH_RULE `!m. (0 = m) \/ 0 < m`;;
let LESS_OR = ARITH_RULE `!m n. m < n ==> (SUC m) <= n`;;
let SUB_OLD = `(!m. 0 - m = 0) /\
                 (!m n. (SUC m) - n = (if m < n then 0 else SUC(m - n)))`;;

(*============================================================================*)
(* Various useful tactics, conversions etc.                                   *)
(*============================================================================*)

(*----------------------------------------------------------------------------*)
(* SYM_CANON_CONV - Canonicalizes single application of symmetric operator    *)
(* Rewrites `so as to make fn true`, e.g. fn = $<< or fn = curry$= `1` o fst  *)
(*----------------------------------------------------------------------------*)

let SYM_CANON_CONV sym fn =
  REWR_CONV sym o
  check (not o fn o ((snd o dest_comb) F_F I) o dest_comb);;

(*----------------------------------------------------------------------------*)
(* IMP_SUBST_TAC - Implicational substitution for deepest matchable term      *)
(*----------------------------------------------------------------------------*)

let (IMP_SUBST_TAC:thm_tactic) =
  fun th (asl,w) ->
    let tms = find_terms (can (PART_MATCH (lhs o snd o dest_imp) th)) w in
    let tm1 = hd (sort free_in tms) in
    let th1 = PART_MATCH (lhs o snd o dest_imp) th tm1 in
    let (a,(l,r)) = (I F_F dest_eq) (dest_imp (concl th1)) in
    let gv = genvar (type_of l) in
    let pat = subst[gv,l] w in
    null_meta,
    [(asl,a); (asl,subst[(r,gv)] pat)],
    fun i [t1;t2] -> SUBST[(SYM(MP th1 t1),gv)] pat t2;;

(*---------------------------------------------------------------*)
(* EXT_CONV `!x. f x = g x` = |- (!x. f x = g x) = (f = g)       *)
(*---------------------------------------------------------------*)

let EXT_CONV =  SYM o uncurry X_FUN_EQ_CONV o
      (I F_F (mk_eq o (rator F_F rator) o dest_eq)) o dest_forall;;

(*----------------------------------------------------------------------------*)
(* EQUAL_TAC - Strip down to unequal core (usually too enthusiastic)          *)
(*----------------------------------------------------------------------------*)

let EQUAL_TAC = REPEAT(FIRST [AP_TERM_TAC; AP_THM_TAC; ABS_TAC]);;

(*----------------------------------------------------------------------------*)
(* X_BETA_CONV `v` `tm[v]` = |- tm[v] = (\v. tm[v]) v                         *)
(*----------------------------------------------------------------------------*)

let X_BETA_CONV v tm =
  SYM(BETA_CONV(mk_comb(mk_abs(v,tm),v)));;

(*----------------------------------------------------------------------------*)
(* EXACT_CONV - Rewrite with theorem matching exactly one in a list           *)
(*----------------------------------------------------------------------------*)

let EXACT_CONV =
  ONCE_DEPTH_CONV o FIRST_CONV o
  map (fun t -> K t o check((=)(lhs(concl t))));;

(*----------------------------------------------------------------------------*)
(* Rather ad-hoc higher-order fiddling conversion                             *)
(* |- (\x. f t1[x] ... tn[x]) = (\x. f ((\x. t1[x]) x) ... ((\x. tn[x]) x))   *)
(*----------------------------------------------------------------------------*)

let HABS_CONV tm =
  let v,bod = dest_abs tm in
  let hop,pl = strip_comb bod in
  let eql = rev(map (X_BETA_CONV v) pl) in
  ABS v (itlist (C(curry MK_COMB)) eql (REFL hop));;

(*----------------------------------------------------------------------------*)
(* Expand an abbreviation                                                     *)
(*----------------------------------------------------------------------------*)

let EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
  check((=) s o fst o dest_var o rhs o concl)) THEN BETA_TAC;;

(* ------------------------------------------------------------------------- *)
(* Set up the reals.                                                         *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let real_le = `!x y. x <= y <=> ~(y < x)`;;

(* ------------------------------------------------------------------------- *)
(* Link a few theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

let REAL_10 = REAL_ARITH `~(&1 = &0)`;;

let REAL_LDISTRIB = REAL_ADD_LDISTRIB;;

let  REAL_LT_IADD = REAL_ARITH `!x y z. y < z ==> x + y < x + z`;;

(*----------------------------------------------------------------------------*)
(* Prove lots of boring field theorems                                        *)
(*----------------------------------------------------------------------------*)

let REAL_MUL_RID = `!x. x * &1 = x`;;

let REAL_MUL_RINV = `!x. ~(x = &0) ==> (x * (inv x) = &1)`;;

let REAL_RDISTRIB = `!x y z. (x + y) * z = (x * z) + (y * z)`;;

let REAL_EQ_LADD = `!x y z. (x + y = x + z) <=> (y = z)`;;

let REAL_EQ_RADD = `!x y z. (x + z = y + z) <=> (x = y)`;;

let REAL_ADD_LID_UNIQ = `!x y. (x + y = y) <=> (x = &0)`;;

let REAL_ADD_RID_UNIQ = `!x y. (x + y = x) <=> (y = &0)`;;

let REAL_LNEG_UNIQ = `!x y. (x + y = &0) <=> (x = --y)`;;

let REAL_RNEG_UNIQ = `!x y. (x + y = &0) <=> (y = --x)`;;

let REAL_NEG_ADD = `!x y. --(x + y) = (--x) + (--y)`;;

let REAL_MUL_LZERO = `!x. &0 * x = &0`;;

let REAL_MUL_RZERO = `!x. x * &0 = &0`;;

let REAL_NEG_LMUL = `!x y. --(x * y) = (--x) * y`;;

let REAL_NEG_RMUL = `!x y. --(x * y) = x * (--y)`;;

let REAL_NEG_NEG = `!x. --(--x) = x`;;

let REAL_NEG_MUL2 = `!x y. (--x) * (--y) = x * y`;;

let REAL_LT_LADD = `!x y z. (x + y) < (x + z) <=> y < z`;;

let REAL_LT_RADD = `!x y z. (x + z) < (y + z) <=> x < y`;;

let REAL_NOT_LT = `!x y. ~(x < y) <=> y <= x`;;

let REAL_LT_ANTISYM = `!x y. ~(x < y /\ y < x)`;;

let REAL_LT_GT = `!x y. x < y ==> ~(y < x)`;;

let REAL_NOT_LE = `!x y. ~(x <= y) <=> y < x`;;

let REAL_LE_TOTAL = `!x y. x <= y \/ y <= x`;;

let REAL_LE_REFL = `!x. x <= x`;;

let REAL_LE_LT = `!x y. x <= y <=> x < y \/ (x = y)`;;

let REAL_LT_LE = `!x y. x < y <=> x <= y /\ ~(x = y)`;;

let REAL_LT_IMP_LE = `!x y. x < y ==> x <= y`;;

let REAL_LTE_TRANS = `!x y z. x < y /\ y <= z ==> x < z`;;

let REAL_LE_TRANS = `!x y z. x <= y /\ y <= z ==> x <= z`;;

let REAL_NEG_LT0 = `!x. (--x) < &0 <=> &0 < x`;;

let REAL_NEG_GT0 = `!x. &0 < (--x) <=> x < &0`;;

let REAL_NEG_LE0 = `!x. (--x) <= &0 <=> &0 <= x`;;

let REAL_NEG_GE0 = `!x. &0 <= (--x) <=> x <= &0`;;

let REAL_LT_NEGTOTAL = `!x. (x = &0) \/ (&0 < x) \/ (&0 < --x)`;;

let REAL_LE_NEGTOTAL = `!x. &0 <= x \/ &0 <= --x`;;

let REAL_LE_MUL = `!x y. &0 <= x /\ &0 <= y ==> &0 <= (x * y)`;;

let REAL_LE_SQUARE = `!x. &0 <= x * x`;;

let REAL_LT_01 = `&0 < &1`;;

let REAL_LE_LADD = `!x y z. (x + y) <= (x + z) <=> y <= z`;;

let REAL_LE_RADD = `!x y z. (x + z) <= (y + z) <=> x <= y`;;

let REAL_LT_ADD2 = `!w x y z. w < x /\ y < z ==> (w + y) < (x + z)`;;

let REAL_LT_ADD = `!x y. &0 < x /\ &0 < y ==> &0 < (x + y)`;;

let REAL_LT_ADDNEG = `!x y z. y < (x + (--z)) <=> (y + z) < x`;;

let REAL_LT_ADDNEG2 = `!x y z. (x + (--y)) < z <=> x < (z + y)`;;

let REAL_LT_ADD1 = `!x y. x <= y ==> x < (y + &1)`;;

let REAL_SUB_ADD = `!x y. (x - y) + y = x`;;

let REAL_SUB_ADD2 = `!x y. y + (x - y) = x`;;

let REAL_SUB_REFL = `!x. x - x = &0`;;

let REAL_SUB_0 = `!x y. (x - y = &0) <=> (x = y)`;;

let REAL_LE_DOUBLE = `!x. &0 <= x + x <=> &0 <= x`;;

let REAL_LE_NEGL = `!x. (--x <= x) <=> (&0 <= x)`;;

let REAL_LE_NEGR = `!x. (x <= --x) <=> (x <= &0)`;;

let REAL_NEG_EQ0 = `!x. (--x = &0) <=> (x = &0)`;;

let REAL_NEG_0 = `--(&0) = &0`;;

let REAL_NEG_SUB = `!x y. --(x - y) = y - x`;;

let REAL_SUB_LT = `!x y. &0 < x - y <=> y < x`;;

let REAL_SUB_LE = `!x y. &0 <= (x - y) <=> y <= x`;;

let REAL_EQ_LMUL = `!x y z. (x * y = x * z) <=> (x = &0) \/ (y = z)`;;

let REAL_EQ_RMUL = `!x y z. (x * z = y * z) <=> (z = &0) \/ (x = y)`;;

let REAL_SUB_LDISTRIB = `!x y z. x * (y - z) = (x * y) - (x * z)`;;

let REAL_SUB_RDISTRIB = `!x y z. (x - y) * z = (x * z) - (y * z)`;;

let REAL_NEG_EQ = `!x y. (--x = y) <=> (x = --y)`;;

let REAL_NEG_MINUS1 = `!x. --x = (--(&1)) * x`;;

let REAL_INV_NZ = `!x. ~(x = &0) ==> ~(inv x = &0)`;;

let REAL_INVINV = `!x. ~(x = &0) ==> (inv (inv x) = x)`;;

let REAL_LT_IMP_NE = `!x y. x < y ==> ~(x = y)`;;

let REAL_INV_POS = `!x. &0 < x ==> &0 < inv x`;;

let REAL_LT_LMUL_0 = `!x y. &0 < x ==> (&0 < (x * y) <=> &0 < y)`;;

let REAL_LT_RMUL_0 = `!x y. &0 < y ==> (&0 < (x * y) <=> &0 < x)`;;

let REAL_LT_LMUL_EQ = `!x y z. &0 < x ==> ((x * y) < (x * z) <=> y < z)`;;

let REAL_LT_RMUL_EQ = `!x y z. &0 < z ==> ((x * z) < (y * z) <=> x < y)`;;

let REAL_LT_RMUL_IMP = `!x y z. x < y /\ &0 < z ==> (x * z) < (y * z)`;;

let REAL_LT_LMUL_IMP = `!x y z. y < z  /\ &0 < x ==> (x * y) < (x * z)`;;

let REAL_LINV_UNIQ = `!x y. (x * y = &1) ==> (x = inv y)`;;

let REAL_RINV_UNIQ = `!x y. (x * y = &1) ==> (y = inv x)`;;

let REAL_NEG_INV = `!x. ~(x = &0) ==> (--(inv x) = inv(--x))`;;

let REAL_INV_1OVER = `!x. inv x = &1 / x`;;

(*----------------------------------------------------------------------------*)
(* Prove homomorphisms for the inclusion map                                  *)
(*----------------------------------------------------------------------------*)

let REAL = `!n. &(SUC n) = &n + &1`;;

let REAL_POS = `!n. &0 <= &n`;;

let REAL_LE = `!m n. &m <= &n <=> m <= n`;;

let REAL_LT = `!m n. &m < &n <=> m < n`;;

let REAL_INJ = `!m n. (&m = &n) <=> (m = n)`;;

let REAL_ADD = `!m n. &m + &n = &(m + n)`;;

let REAL_MUL = `!m n. &m * &n = &(m * n)`;;

(*----------------------------------------------------------------------------*)
(* Now more theorems                                                          *)
(*----------------------------------------------------------------------------*)

let REAL_INV1 = `inv(&1) = &1`;;

let REAL_DIV_LZERO = `!x. &0 / x = &0`;;

let REAL_LT_NZ = `!n. ~(&n = &0) <=> (&0 < &n)`;;

let REAL_NZ_IMP_LT = `!n. ~(n = 0) ==> &0 < &n`;;

let REAL_LT_RDIV_0 = `!y z. &0 < z ==> (&0 < (y / z) <=> &0 < y)`;;

let REAL_LT_RDIV = `!x y z. &0 < z ==> ((x / z) < (y / z) <=> x < y)`;;

let REAL_LT_FRACTION_0 = `!n d. ~(n = 0) ==> (&0 < (d / &n) <=> &0 < d)`;;

let REAL_LT_MULTIPLE = `!n d. 1 < n ==> (d < (&n * d) <=> &0 < d)`;;

let REAL_LT_FRACTION = `!n d. (1 < n) ==> ((d / &n) < d <=> &0 < d)`;;

let REAL_LT_HALF1 = `!d. &0 < (d / &2) <=> &0 < d`;;

let REAL_LT_HALF2 = `!d. (d / &2) < d <=> &0 < d`;;

let REAL_DOUBLE = `!x. x + x = &2 * x`;;

let REAL_HALF_DOUBLE = `!x. (x / &2) + (x / &2) = x`;;

let REAL_SUB_SUB = `!x y. (x - y) - x = --y`;;

let REAL_LT_ADD_SUB = `!x y z. (x + y) < z <=> x < (z - y)`;;

let REAL_LT_SUB_RADD = `!x y z. (x - y) < z <=> x < z + y`;;

let REAL_LT_SUB_LADD = `!x y z. x < (y - z) <=> (x + z) < y`;;

let REAL_LE_SUB_LADD = `!x y z. x <= (y - z) <=> (x + z) <= y`;;

let REAL_LE_SUB_RADD = `!x y z. (x - y) <= z <=> x <= z + y`;;

let REAL_LT_NEG2 = `!x y. --x < --y <=> y < x`;;

let REAL_LE_NEG2 = `!x y. --x <= --y <=> y <= x`;;

let REAL_SUB_LZERO = `!x. &0 - x = --x`;;

let REAL_SUB_RZERO = `!x. x - &0 = x`;;

let REAL_LTE_ADD2 = `!w x y z. w < x /\ y <= z ==> (w + y) < (x + z)`;;

let REAL_LTE_ADD = `!x y. &0 < x /\ &0 <= y ==> &0 < (x + y)`;;

let REAL_LT_MUL2_ALT = `!x1 x2 y1 y2. &0 <= x1 /\ &0 <= y1 /\ x1 < x2 /\ y1 < y2 ==>
        (x1 * y1) < (x2 * y2)`;;

let REAL_SUB_LNEG = `!x y. (--x) - y = --(x + y)`;;

let REAL_SUB_RNEG = `!x y. x - (--y) = x + y`;;

let REAL_SUB_NEG2 = `!x y. (--x) - (--y) = y - x`;;

let REAL_SUB_TRIANGLE = `!a b c. (a - b) + (b - c) = a - c`;;

let REAL_INV_MUL_WEAK = `!x y. ~(x = &0) /\ ~(y = &0) ==>
             (inv(x * y) = inv(x) * inv(y))`;;

let REAL_LE_LMUL_LOCAL = `!x y z. &0 < x ==> ((x * y) <= (x * z) <=> y <= z)`;;

let REAL_LE_RMUL_EQ = `!x y z. &0 < z ==> ((x * z) <= (y * z) <=> x <= y)`;;

let REAL_SUB_INV2 = `!x y. ~(x = &0) /\ ~(y = &0) ==>
                (inv(x) - inv(y) = (y - x) / (x * y))`;;

let REAL_SUB_SUB2 = `!x y. x - (x - y) = y`;;

let REAL_MEAN = `!x y. x < y ==> ?z. x < z /\ z < y`;;

let REAL_EQ_LMUL2 = `!x y z. ~(x = &0) ==> ((y = z) <=> (x * y = x * z))`;;

let REAL_LE_MUL2V = `!x1 x2 y1 y2.
    (& 0) <= x1 /\ (& 0) <= y1 /\ x1 <= x2 /\ y1 <= y2 ==>
    (x1 * y1) <= (x2 * y2)`;;

let REAL_LE_LDIV = `!x y z. &0 < x /\ y <= (z * x) ==> (y / x) <= z`;;

let REAL_LE_RDIV = `!x y z. &0 < x /\ (y * x) <= z ==> y <= (z / x)`;;

let REAL_LT_1 = `!x y. &0 <= x /\ x < y ==> (x / y) < &1`;;

let REAL_LE_LMUL_IMP = `!x y z. &0 <= x /\ y <= z ==> (x * y) <= (x * z)`;;

let REAL_LE_RMUL_IMP = `!x y z. &0 <= x /\ y <= z ==> (y * x) <= (z * x)`;;

let REAL_INV_LT1 = `!x. &0 < x /\ x < &1 ==> &1 < inv(x)`;;

let REAL_LT_IMP_NZ = `!x. &0 < x ==> ~(x = &0)`;;

let REAL_EQ_RMUL_IMP = `!x y z. ~(z = &0) /\ (x * z = y * z) ==> (x = y)`;;

let REAL_EQ_LMUL_IMP = `!x y z. ~(x = &0) /\ (x * y = x * z) ==> (y = z)`;;

let REAL_FACT_NZ = `!n. ~(&(FACT n) = &0)`;;

let REAL_POSSQ = `!x. &0 < (x * x) <=> ~(x = &0)`;;

let REAL_SUMSQ = `!x y. ((x * x) + (y * y) = &0) <=> (x = &0) /\ (y = &0)`;;

let REAL_EQ_NEG = `!x y. (--x = --y) <=> (x = y)`;;

let REAL_DIV_MUL2 = `!x z. ~(x = &0) /\ ~(z = &0) ==> !y. y / z = (x * y) / (x * z)`;;

let REAL_MIDDLE1 = `!a b. a <= b ==> a <= (a + b) / &2`;;

let REAL_MIDDLE2 = `!a b. a <= b ==> ((a + b) / &2) <= b`;;

(*----------------------------------------------------------------------------*)
(* Define usual norm (absolute distance) on the real line                     *)
(*----------------------------------------------------------------------------*)

let ABS_ZERO = `!x. (abs(x) = &0) <=> (x = &0)`;;

let ABS_0 = `abs(&0) = &0`;;

let ABS_1 = `abs(&1) = &1`;;

let ABS_NEG = `!x. abs(--x) = abs(x)`;;

let ABS_TRIANGLE = `!x y. abs(x + y) <= abs(x) + abs(y)`;;

let ABS_POS = `!x. &0 <= abs(x)`;;

let ABS_MUL = `!x y. abs(x * y) = abs(x) * abs(y)`;;

let ABS_LT_MUL2 = `!w x y z. abs(w) < y /\ abs(x) < z ==> abs(w * x) < (y * z)`;;

let ABS_SUB = `!x y. abs(x - y) = abs(y - x)`;;

let ABS_NZ = `!x. ~(x = &0) <=> &0 < abs(x)`;;

let ABS_INV = `!x. ~(x = &0) ==> (abs(inv x) = inv(abs(x)))`;;

let ABS_ABS = `!x. abs(abs(x)) = abs(x)`;;

let ABS_LE = `!x. x <= abs(x)`;;

let ABS_REFL = `!x. (abs(x) = x) <=> &0 <= x`;;

let ABS_N = `!n. abs(&n) = &n`;;

let ABS_BETWEEN = `!x y d. &0 < d /\ ((x - d) < y) /\ (y < (x + d)) <=> abs(y - x) < d`;;

let ABS_BOUND = `!x y d. abs(x - y) < d ==> y < (x + d)`;;

let ABS_STILLNZ = `!x y. abs(x - y) < abs(y) ==> ~(x = &0)`;;

let ABS_CASES = `!x. (x = &0) \/ &0 < abs(x)`;;

let ABS_BETWEEN1 = `!x y z. x < z /\ (abs(y - x)) < (z - x) ==> y < z`;;

let ABS_SIGN = `!x y. abs(x - y) < y ==> &0 < x`;;

let ABS_SIGN2 = `!x y. abs(x - y) < --y ==> x < &0`;;

let ABS_DIV = `!y. ~(y = &0) ==> !x. abs(x / y) = abs(x) / abs(y)`;;

let ABS_CIRCLE = `!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)`;;

let REAL_SUB_ABS = `!x y. (abs(x) - abs(y)) <= abs(x - y)`;;

let ABS_SUB_ABS = `!x y. abs(abs(x) - abs(y)) <= abs(x - y)`;;

let ABS_BETWEEN2 = `!x0 x y0 y. x0 < y0 /\ abs(x - x0) < (y0 - x0) / &2 /\
                          abs(y - y0) < (y0 - x0) / &2
        ==> x < y`;;

let ABS_BOUNDS = `!x k. abs(x) <= k <=> --k <= x /\ x <= k`;;

(*----------------------------------------------------------------------------*)
(* Define integer powers                                                      *)
(*----------------------------------------------------------------------------*)

let pow = real_pow;;

let POW_0 = `!n. &0 pow (SUC n) = &0`;;

let POW_NZ = `!c n. ~(c = &0) ==> ~(c pow n = &0)`;;

let POW_INV = `!c n. ~(c = &0) ==> (inv(c pow n) = (inv c) pow n)`;;

let POW_ABS = `!c n. abs(c) pow n = abs(c pow n)`;;

let POW_PLUS1 = `!e n. &0 < e ==> (&1 + (&n * e)) <= (&1 + e) pow n`;;

let POW_ADD = `!c m n. c pow (m + n) = (c pow m) * (c pow n)`;;

let POW_1 = `!x. x pow 1 = x`;;

let POW_2 = `!x. x pow 2 = x * x`;;

let POW_POS = `!x n. &0 <= x ==> &0 <= (x pow n)`;;

let POW_LE = `!n x y. &0 <= x /\ x <= y ==> (x pow n) <= (y pow n)`;;

let POW_M1 = `!n. abs((--(&1)) pow n) = &1`;;

let POW_MUL = `!n x y. (x * y) pow n = (x pow n) * (y pow n)`;;

let REAL_LE_SQUARE_POW = `!x. &0 <= x pow 2`;;

let ABS_POW2 = `!x. abs(x pow 2) = x pow 2`;;

let REAL_LE1_POW2 = `!x. &1 <= x ==> &1 <= (x pow 2)`;;

let REAL_LT1_POW2 = `!x. &1 < x ==> &1 < (x pow 2)`;;

let POW_POS_LT = `!x n. &0 < x ==> &0 < (x pow (SUC n))`;;

let POW_2_LE1 = `!n. &1 <= &2 pow n`;;

let POW_2_LT = `!n. &n < &2 pow n`;;

let POW_MINUS1 = `!n. (--(&1)) pow (2 * n) = &1`;;

(*----------------------------------------------------------------------------*)
(* Derive the supremum property for an arbitrary bounded nonempty set         *)
(*----------------------------------------------------------------------------*)

let REAL_SUP_EXISTS = `!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) <=> y < s)`;;

let sup_def = new_definition
 `sup s = @a. (!x. x IN s ==> x <= a) /\
              (!b. (!x. x IN s ==> x <= b) ==> a <= b)`;;

let sup = `sup P = @s. !y. (?x. P x /\ y < x) <=> y < s`;;

let REAL_SUP = `!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. (?x. P x /\ y < x) <=> y < sup P)`;;

let REAL_SUP_UBOUND = `!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. P y ==> y <= sup P)`;;

let SETOK_LE_LT = `!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) <=>
       (?x. P x) /\ (?z. !x. P x ==> x < z)`;;

let REAL_SUP_LE = `!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
           (!y. (?x. P x /\ y < x) <=> y < sup P)`;;

let REAL_SUP_UBOUND_LE = `!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
          (!y. P y ==> y <= sup P)`;;

(*----------------------------------------------------------------------------*)
(* Prove the Archimedean property                                             *)
(*----------------------------------------------------------------------------*)

let REAL_ARCH_SIMPLE = `!x. ?n. x <= &n`;;

let REAL_ARCH = `!x. &0 < x ==> !y. ?n. y < &n * x`;;

let REAL_ARCH_LEAST = `!y. &0 < y ==> !x. &0 <= x ==>
                        ?n. (&n * y) <= x /\ x < (&(SUC n) * y)`;;

let REAL_POW_LBOUND = `!x n. &0 <= x ==> &1 + &n * x <= (&1 + x) pow n`;;

let REAL_ARCH_POW = `!x y. &1 < x ==> ?n. y < x pow n`;;

let REAL_ARCH_POW2 = `!x. ?n. x < &2 pow n`;;

(* ========================================================================= *)
(* Finite sums. NB: sum(m,n) f = f(m) + f(m+1) + ... + f(m+n-1)              *)
(* ========================================================================= *)

prioritize_real();;

make_overloadable "sum" `:A->(B->real)->real`;;

overload_interface("sum",`sum:(A->bool)->(A->real)->real`);;
overload_interface("sum",`psum:(num#num)->(num->real)->real`);;

let sum_EXISTS = `?sum. (!f n. sum(n,0) f = &0) /\
         (!f m n. sum(n,SUC m) f = sum(n,m) f + f(n + m))`;;

let sum_DEF = new_specification ["psum"] sum_EXISTS;;

let sum = `(sum(n,0) f = &0) /\
   (sum(n,SUC m) f = sum(n,m) f + f(n + m))`;;

(* ------------------------------------------------------------------------- *)
(* Relation to the standard notion.                                          *)
(* ------------------------------------------------------------------------- *)

let PSUM_SUM = `!f m n. sum(m,n) f = sum {i | m <= i /\ i < m + n} f`;;

let PSUM_SUM_NUMSEG = `!f m n. ~(m = 0 /\ n = 0) ==> sum(m,n) f = sum(m..(m+n)-1) f`;;

(* ------------------------------------------------------------------------- *)
(* Stuff about sums.                                                         *)
(* ------------------------------------------------------------------------- *)

let SUM_TWO = `!f n p. sum(0,n) f + sum(n,p) f = sum(0,n + p) f`;;

let SUM_DIFF = `!f m n. sum(m,n) f = sum(0,m + n) f - sum(0,m) f`;;

let ABS_SUM = `!f m n. abs(sum(m,n) f) <= sum(m,n) (\n. abs(f n))`;;

let SUM_LE = `!f g m n. (!r. m <= r /\ r < n + m ==> f(r) <= g(r))
        ==> (sum(m,n) f <= sum(m,n) g)`;;

let SUM_EQ = `!f g m n. (!r. m <= r /\ r < (n + m) ==> (f(r) = g(r)))
        ==> (sum(m,n) f = sum(m,n) g)`;;

let SUM_POS = `!f. (!n. &0 <= f(n)) ==> !m n. &0 <= sum(m,n) f`;;

let SUM_POS_GEN = `!f m n.
     (!n. m <= n ==> &0 <= f(n))
     ==> &0 <= sum(m,n) f`;;

let SUM_ABS = `!f m n. abs(sum(m,n) (\m. abs(f m))) = sum(m,n) (\m. abs(f m))`;;

let SUM_ABS_LE = `!f m n. abs(sum(m,n) f) <= sum(m,n)(\n. abs(f n))`;;

let SUM_ZERO = `!f N. (!n. n >= N ==> (f(n) = &0)) ==>
         (!m n. m >= N ==> (sum(m,n) f = &0))`;;

let SUM_ADD = `!f g m n. sum(m,n) (\n. f(n) + g(n)) = sum(m,n) f + sum(m,n) g`;;

let SUM_CMUL = `!f c m n. sum(m,n) (\n. c * f(n)) = c * sum(m,n) f`;;

let SUM_NEG = `!f n d. sum(n,d) (\n. --(f n)) = --(sum(n,d) f)`;;

let SUM_SUB = `!f g m n. sum(m,n)(\n. (f n) - (g n)) = sum(m,n) f - sum(m,n) g`;;

let SUM_SUBST = `!f g m n. (!p. m <= p /\ p < (m + n) ==> (f p = g p))
        ==> (sum(m,n) f = sum(m,n) g)`;;

let SUM_NSUB = `!n f c. sum(0,n) f - (&n * c) = sum(0,n)(\p. f(p) - c)`;;

let SUM_BOUND = `!f K m n. (!p. m <= p /\ p < (m + n) ==> (f(p) <= K))
        ==> (sum(m,n) f <= (&n * K))`;;

let SUM_GROUP = `!n k f. sum(0,n)(\m. sum(m * k,k) f) = sum(0,n * k) f`;;

let SUM_1 = `!f n. sum(n,1) f = f(n)`;;

let SUM_2 = `!f n. sum(n,2) f = f(n) + f(n + 1)`;;

let SUM_OFFSET = `!f n k. sum(0,n)(\m. f(m + k)) = sum(0,n + k) f - sum(0,k) f`;;

let SUM_REINDEX = `!f m k n. sum(m + k,n) f = sum(m,n)(\r. f(r + k))`;;

let SUM_0 = `!m n. sum(m,n)(\r. &0) = &0`;;

let SUM_CANCEL = `!f n d. sum(n,d) (\n. f(SUC n) - f(n)) = f(n + d) - f(n)`;;

let SUM_HORNER = `!f n x. sum(0,SUC n)(\i. f(i) * x pow i) =
           f(0) + x * sum(0,n)(\i. f(SUC i) * x pow i)`;;

let SUM_CONST = `!c n. sum(0,n) (\m. c) = &n * c`;;

let SUM_SPLIT = `!f n p. sum(m,n) f + sum(m + n,p) f = sum(m,n + p) f`;;

let SUM_SWAP = `!f m1 n1 m2 n2.
        sum(m1,n1) (\a. sum(m2,n2) (\b. f a b)) =
        sum(m2,n2) (\b. sum(m1,n1) (\a. f a b))`;;

let SUM_EQ_0 = `(!r. m <= r /\ r < m + n ==> (f(r) = &0)) ==> (sum(m,n) f = &0)`;;

let SUM_MORETERMS_EQ = `!m n p.
      n <= p /\ (!r. m + n <= r /\ r < m + p ==> (f(r) = &0))
      ==> (sum(m,p) f = sum(m,n) f)`;;

let SUM_DIFFERENCES_EQ = `!m n p.
      n <= p /\ (!r. m + n <= r /\ r < m + p ==> (f(r) = g(r)))
      ==> (sum(m,p) f - sum(m,n) f = sum(m,p) g - sum(m,n) g)`;;

(* ------------------------------------------------------------------------- *)
(* A conversion to evaluate summations (not clear it belongs here...)        *)
(* ------------------------------------------------------------------------- *)

let REAL_SUM_CONV =
  let sum_tm = `sum` in
  let pth = `sum(0,1) f = f 0`;;
parse_as_infix("re_intersect",(17,"right"));;
parse_as_infix("re_subset",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Minimal amount of set notation is convenient                               *)
(*----------------------------------------------------------------------------*)

let re_Union = new_definition(
  `re_Union S = \x:A. ?s. S s /\ s x`);;

let re_union = new_definition(
  `P re_union Q = \x:A. P x \/ Q x`);;

let re_intersect = new_definition
  `P re_intersect Q = \x:A. P x /\ Q x`;;

let re_null = new_definition(
  `re_null = \x:A. F`);;

let re_universe = new_definition(
  `re_universe = \x:A. T`);;

let re_subset = new_definition(
  `P re_subset Q <=> !x:A. P x ==> Q x`);;

let re_compl = new_definition(
  `re_compl S = \x:A. ~(S x)`);;

let SUBSETA_REFL = `!S:A->bool. S re_subset S`;;

let COMPL_MEM = `!S:A->bool. !x. S x <=> ~(re_compl S x)`;;

let SUBSETA_ANTISYM = `!P:A->bool. !Q. P re_subset Q /\ Q re_subset P <=> (P = Q)`;;

let SUBSETA_TRANS = `!P:A->bool. !Q R. P re_subset Q /\ Q re_subset R ==> P re_subset R`;;

(*----------------------------------------------------------------------------*)
(* Characterize an (A)topology                                                *)
(*----------------------------------------------------------------------------*)

let istopology = new_definition(
  `!L:(A->bool)->bool. istopology L <=>
            L re_null /\
            L re_universe /\
     (!a b. L a /\ L b ==> L (a re_intersect b)) /\
       (!P. P re_subset L ==> L (re_Union P))`);;

let topology_tybij = new_type_definition "topology" ("topology","open")
 (prove(`?t:(A->bool)->bool. istopology t`,
        EXISTS_TAC `re_universe:(A->bool)->bool` THEN
        REWRITE_TAC[istopology; re_universe]));;

let TOPOLOGY = `!L:(A)topology. open(L) re_null /\
                   open(L) re_universe /\
            (!x y. open(L) x /\ open(L) y ==> open(L) (x re_intersect y)) /\
              (!P. P re_subset (open L) ==> open(L) (re_Union P))`;;

let TOPOLOGY_UNION = `!L:(A)topology. !P. P re_subset (open L) ==> open(L) (re_Union P)`;;

(*----------------------------------------------------------------------------*)
(* Characterize a neighbourhood of a point relative to a topology             *)
(*----------------------------------------------------------------------------*)

let neigh = new_definition(
  `neigh(top)(N,(x:A)) = ?P. open(top) P /\ P re_subset N /\ P x`);;

(*----------------------------------------------------------------------------*)
(* Prove various properties / characterizations of open sets                  *)
(*----------------------------------------------------------------------------*)

let OPEN_OWN_NEIGH = `!S top. !x:A. open(top) S /\ S x ==> neigh(top)(S,x)`;;

let OPEN_UNOPEN = `!S top. open(top) S <=>
           (re_Union (\P:A->bool. open(top) P /\ P re_subset S) = S)`;;

let OPEN_SUBOPEN = `!S top. open(top) S <=>
           !x:A. S x ==> ?P. P x /\ open(top) P /\ P re_subset S`;;

let OPEN_NEIGH = `!S top. open(top) S = !x:A. S x ==> ?N. neigh(top)(N,x) /\ N re_subset S`;;

(*----------------------------------------------------------------------------*)
(* Characterize closed sets in a topological space                            *)
(*----------------------------------------------------------------------------*)

let closed = new_definition(
  `closed(L:(A)topology) S = open(L)(re_compl S)`);;

(*----------------------------------------------------------------------------*)
(* Define limit point in topological space                                    *)
(*----------------------------------------------------------------------------*)

let limpt = new_definition(
  `limpt(top) x S <=>
      !N:A->bool. neigh(top)(N,x) ==> ?y. ~(x = y) /\ S y /\ N y`);;

(*----------------------------------------------------------------------------*)
(* Prove that a set is closed iff it contains all its limit points            *)
(*----------------------------------------------------------------------------*)

let CLOSED_LIMPT = `!top S. closed(top) S <=> (!x:A. limpt(top) x S ==> S x)`;;

(*----------------------------------------------------------------------------*)
(* Characterize an (A)metric                                                  *)
(*----------------------------------------------------------------------------*)

let ismet = new_definition(
  `ismet (m:A#A->real) <=> (!x y. (m(x,y) = &0) <=> (x = y)) /\
                           (!x y z. m(y,z) <= m(x,y) + m(x,z))`);;

let metric_tybij = new_type_definition "metric" ("metric","mdist")
      (prove(`?m:(A#A->real). ismet m`,
        EXISTS_TAC `\((x:A),(y:A)). if x = y then &0 else &1` THEN
        REWRITE_TAC[ismet] THEN
        CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        CONJ_TAC THEN REPEAT GEN_TAC THENL
         [BOOL_CASES_TAC `x:A = y` THEN REWRITE_TAC[REAL_10];
          REPEAT COND_CASES_TAC THEN
          ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID; REAL_LE_REFL; REAL_LE_01]
          THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_LID] THEN
          TRY(MATCH_MP_TAC REAL_LE_ADD2) THEN
          REWRITE_TAC[REAL_LE_01; REAL_LE_REFL] THEN
          FIRST_ASSUM(UNDISCH_TAC o check is_neg o concl) THEN
          EVERY_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]));;

(*----------------------------------------------------------------------------*)
(* Derive the metric properties                                               *)
(*----------------------------------------------------------------------------*)

let METRIC_ISMET = `!m:(A)metric. ismet (mdist m)`;;

let METRIC_ZERO = `!m:(A)metric. !x y. ((mdist m)(x,y) = &0) <=> (x = y)`;;

let METRIC_SAME = `!m:(A)metric. !x. (mdist m)(x,x) = &0`;;

let METRIC_POS = `!m:(A)metric. !x y. &0 <= (mdist m)(x,y)`;;

let METRIC_SYM = `!m:(A)metric. !x y. (mdist m)(x,y) = (mdist m)(y,x)`;;

let METRIC_TRIANGLE = `!m:(A)metric. !x y z. (mdist m)(x,z) <= (mdist m)(x,y) + (mdist m)(y,z)`;;

let METRIC_NZ = `!m:(A)metric. !x y. ~(x = y) ==> &0 < (mdist m)(x,y)`;;

(*----------------------------------------------------------------------------*)
(* Now define metric topology and prove equivalent definition of `open`       *)
(*----------------------------------------------------------------------------*)

let mtop = new_definition(
  `!m:(A)metric. mtop m =
    topology(\S. !x. S x ==> ?e. &0 < e /\ (!y. (mdist m)(x,y) < e ==> S y))`);;

let mtop_istopology = `!m:(A)metric. istopology
    (\S. !x. S x ==> ?e. &0 < e /\ (!y. (mdist m)(x,y) < e ==> S y))`;;

let MTOP_OPEN = `!m:(A)metric. open(mtop m) S <=>
      (!x. S x ==> ?e. &0 < e /\ (!y. (mdist m(x,y)) < e ==> S y))`;;

(*----------------------------------------------------------------------------*)
(* Define open ball in metric space + prove basic properties                  *)
(*----------------------------------------------------------------------------*)

let ball = new_definition(
  `!m:(A)metric. !x e. ball(m)(x,e) = \y. (mdist m)(x,y) < e`);;

let BALL_OPEN = `!m:(A)metric. !x e. &0 < e ==> open(mtop(m))(ball(m)(x,e))`;;

let BALL_NEIGH = `!m:(A)metric. !x e. &0 < e ==> neigh(mtop(m))(ball(m)(x,e),x)`;;

(*----------------------------------------------------------------------------*)
(* Characterize limit point in a metric topology                              *)
(*----------------------------------------------------------------------------*)

let MTOP_LIMPT = `!m:(A)metric. !x S. limpt(mtop m) x S <=>
      !e. &0 < e ==> ?y. ~(x = y) /\ S y /\ (mdist m)(x,y) < e`;;

(*----------------------------------------------------------------------------*)
(* Define the usual metric on the real line                                   *)
(*----------------------------------------------------------------------------*)

let ISMET_R1 = `ismet (\(x,y). abs(y - x))`;;

let mr1 = new_definition(
  `mr1 = metric(\(x,y). abs(y - x))`);;

let MR1_DEF = `!x y. (mdist mr1)(x,y) = abs(y - x)`;;

let MR1_ADD = `!x d. (mdist mr1)(x,x+d) = abs(d)`;;

let MR1_SUB = `!x d. (mdist mr1)(x,x-d) = abs(d)`;;

let MR1_ADD_LE = `!x d. &0 <= d ==> ((mdist mr1)(x,x+d) = d)`;;

let MR1_SUB_LE = `!x d. &0 <= d ==> ((mdist mr1)(x,x-d) = d)`;;

let MR1_ADD_LT = `!x d. &0 < d ==> ((mdist mr1)(x,x+d) = d)`;;

let MR1_SUB_LT = `!x d. &0 < d ==> ((mdist mr1)(x,x-d) = d)`;;

let MR1_BETWEEN1 = `!x y z. x < z /\ (mdist mr1)(x,y) < (z - x) ==> y < z`;;

(*----------------------------------------------------------------------------*)
(* Every real is a limit point of the real line                               *)
(*----------------------------------------------------------------------------*)

let MR1_LIMPT = `!x. limpt(mtop mr1) x re_universe`;;

(*============================================================================*)
(* Theory of Moore-Smith covergence nets, and special cases like sequences    *)
(*============================================================================*)

parse_as_infix ("tends",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Basic definitions: directed set, net, bounded net, pointwise limit         *)
(*----------------------------------------------------------------------------*)

let dorder = new_definition(
  `dorder (g:A->A->bool) <=>
     !x y. g x x /\ g y y ==> ?z. g z z /\ (!w. g w z ==> g w x /\ g w y)`);;

let tends = new_definition
  `(s tends l)(top,g) <=>
      !N:A->bool. neigh(top)(N,l) ==>
            ?n:B. g n n /\ !m:B. g m n ==> N(s m)`;;

let bounded = new_definition(
  `bounded((m:(A)metric),(g:B->B->bool)) f <=>
      ?k x N. g N N /\ (!n. g n N ==> (mdist m)(f(n),x) < k)`);;

let tendsto = new_definition(
  `tendsto((m:(A)metric),x) y z <=>
      &0 < (mdist m)(x,y) /\ (mdist m)(x,y) <= (mdist m)(x,z)`);;

parse_as_infix("-->",(12,"right"));;

override_interface ("-->",`(tends)`);;

let DORDER_LEMMA = `!g:A->A->bool.
      dorder g ==>
        !P Q. (?n. g n n /\ (!m. g m n ==> P m)) /\
              (?n. g n n /\ (!m. g m n ==> Q m))
                  ==> (?n. g n n /\ (!m. g m n ==> P m /\ Q m))`;;

(*----------------------------------------------------------------------------*)
(* Following tactic is useful in the following proofs                         *)
(*----------------------------------------------------------------------------*)

let DORDER_THEN tac th =
  let [t1;t2] = map (rand o rand o body o rand) (conjuncts(concl th)) in
  let dog = (rator o rator o rand o rator o body) t1 in
  let thl = map ((uncurry X_BETA_CONV) o (I F_F rand) o dest_abs) [t1;t2] in
  let th1 = CONV_RULE(EXACT_CONV thl) th in
  let th2 = MATCH_MP DORDER_LEMMA (ASSUME (list_mk_icomb "dorder" [dog])) in
  let th3 = MATCH_MP th2 th1 in
  let th4 = CONV_RULE(EXACT_CONV(map SYM thl)) th3 in
  tac th4;;

(*----------------------------------------------------------------------------*)
(* Show that sequences and pointwise limits in a metric space are directed    *)
(*----------------------------------------------------------------------------*)

let DORDER_NGE = `dorder ((>=) :num->num->bool)`;;

let DORDER_TENDSTO = `!m:(A)metric. !x. dorder(tendsto(m,x))`;;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of limit in a metric topology                     *)
(*----------------------------------------------------------------------------*)

let MTOP_TENDS = `!d g. !x:B->A. !x0. (x --> x0)(mtop(d),g) <=>
     !e. &0 < e ==> ?n. g n n /\ !m. g m n ==> mdist(d)(x(m),x0) < e`;;

(*----------------------------------------------------------------------------*)
(* Prove that a net in a metric topology cannot converge to different limits  *)
(*----------------------------------------------------------------------------*)

let MTOP_TENDS_UNIQ = `!g d. dorder (g:B->B->bool) ==>
      (x --> x0)(mtop(d),g) /\ (x --> x1)(mtop(d),g) ==> (x0:A = x1)`;;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of limit of a sequence in a metric topology       *)
(*----------------------------------------------------------------------------*)

let SEQ_TENDS = `!d:(A)metric. !x x0. (x --> x0)(mtop(d), (>=) :num->num->bool) <=>
     !e. &0 < e ==> ?N. !n. n >= N ==> mdist(d)(x(n),x0) < e`;;

(*----------------------------------------------------------------------------*)
(* And of limit of function between metric spaces                             *)
(*----------------------------------------------------------------------------*)

let LIM_TENDS = `!m1:(A)metric. !m2:(B)metric. !f x0 y0.
      limpt(mtop m1) x0 re_universe ==>
        ((f --> y0)(mtop(m2),tendsto(m1,x0)) <=>
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (mdist m1)(x,x0) /\ (mdist m1)(x,x0) <= d
                ==> (mdist m2)(f(x),y0) < e)`;;

(*----------------------------------------------------------------------------*)
(* Similar, more conventional version, is also true at a limit point          *)
(*----------------------------------------------------------------------------*)

let LIM_TENDS2 = `!m1:(A)metric. !m2:(B)metric. !f x0 y0.
      limpt(mtop m1) x0 re_universe ==>
        ((f --> y0)(mtop(m2),tendsto(m1,x0)) <=>
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (mdist m1)(x,x0) /\ (mdist m1)(x,x0) < d ==>
              (mdist m2)(f(x),y0) < e)`;;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of boundedness for the real line                  *)
(*----------------------------------------------------------------------------*)

let MR1_BOUNDED = `!(g:A->A->bool) f. bounded(mr1,g) f <=>
        ?k N. g N N /\ (!n. g n N ==> abs(f n) < k)`;;

(*----------------------------------------------------------------------------*)
(* Firstly, prove useful forms of null and bounded nets                       *)
(*----------------------------------------------------------------------------*)

let NET_NULL = `!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) <=> ((\n. x(n) - x0) --> &0)(mtop(mr1),g)`;;

let NET_CONV_BOUNDED = `!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) ==> bounded(mr1,g) x`;;

let NET_CONV_NZ = `!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        ?N. g N N /\ (!n. g n N ==> ~(x n = &0))`;;

let NET_CONV_IBOUNDED = `!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        bounded(mr1,g) (\n. inv(x n))`;;

(*----------------------------------------------------------------------------*)
(* Now combining theorems for null nets                                       *)
(*----------------------------------------------------------------------------*)

let NET_NULL_ADD = `!g:A->A->bool. dorder g ==>
        !x y. (x --> &0)(mtop(mr1),g) /\ (y --> &0)(mtop(mr1),g) ==>
                ((\n. x(n) + y(n)) --> &0)(mtop(mr1),g)`;;

let NET_NULL_MUL = `!g:A->A->bool. dorder g ==>
      !x y. bounded(mr1,g) x /\ (y --> &0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) --> &0)(mtop(mr1),g)`;;

let NET_NULL_CMUL = `!g:A->A->bool. !k x.
      (x --> &0)(mtop(mr1),g) ==> ((\n. k * x(n)) --> &0)(mtop(mr1),g)`;;

(*----------------------------------------------------------------------------*)
(* Now real arithmetic theorems for convergent nets                           *)
(*----------------------------------------------------------------------------*)

let NET_ADD = `!g:A->A->bool x x0 y y0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g)
            ==> ((\n. x(n) + y(n)) --> (x0 + y0))(mtop(mr1),g)`;;

let NET_NEG = `!g:A->A->bool x x0.
        dorder g
        ==> ((x --> x0)(mtop(mr1),g) <=>
            ((\n. --(x n)) --> --x0)(mtop(mr1),g))`;;

let NET_SUB = `!g:A->A->bool x x0 y y0.
      dorder g
      ==> (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g)
          ==> ((\n. x(n) - y(n)) --> (x0 - y0))(mtop(mr1),g)`;;

let NET_MUL = `!g:A->A->bool x y x0 y0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g)
            ==> ((\n. x(n) * y(n)) --> (x0 * y0))(mtop(mr1),g)`;;

let NET_INV = `!g:A->A->bool x x0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0)
            ==> ((\n. inv(x(n))) --> inv x0)(mtop(mr1),g)`;;

let NET_DIV = `!g:A->A->bool x x0 y y0.
       dorder g
       ==> (x --> x0)(mtop(mr1),g) /\
           (y --> y0)(mtop(mr1),g) /\ ~(y0 = &0)
           ==> ((\n. x(n) / y(n)) --> (x0 / y0))(mtop(mr1),g)`;;

let NET_ABS = `!x x0. (x --> x0)(mtop(mr1),g) ==>
               ((\n:A. abs(x n)) --> abs(x0))(mtop(mr1),g)`;;

let NET_SUM = `!g. dorder g /\
       ((\x. &0) --> &0)(mtop(mr1),g)
       ==> !m n. (!r. m <= r /\ r < m + n ==> (f r --> l r)(mtop(mr1),g))
                 ==> ((\x. sum(m,n) (\r. f r x)) --> sum(m,n) l)
                     (mtop(mr1),g)`;;

(*----------------------------------------------------------------------------*)
(* Comparison between limits                                                  *)
(*----------------------------------------------------------------------------*)

let NET_LE = `!g:A->A->bool x x0 y y0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\
            (y --> y0)(mtop(mr1),g) /\
            (?N. g N N /\ !n. g n N ==> x(n) <= y(n))
            ==> x0 <= y0`;;

(*============================================================================*)
(* Theory of sequences and series of real numbers                             *)
(*============================================================================*)

parse_as_infix ("tends_num_real",(12,"right"));;

parse_as_infix ("sums",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Specialize net theorems to sequences:num->real                             *)
(*----------------------------------------------------------------------------*)

let tends_num_real = new_definition(
  `x tends_num_real x0 <=> (x tends x0)(mtop(mr1), (>=) :num->num->bool)`);;

override_interface ("-->",`(tends_num_real)`);;

let SEQ = `!x x0. (x --> x0) <=>
          !e. &0 < e ==> ?N. !n. n >= N ==> abs(x(n) - x0) < e`;;

let SEQ_CONST = `!k. (\x. k) --> k`;;

let SEQ_ADD = `!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) + y(n)) --> (x0 + y0)`;;

let SEQ_MUL = `!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) * y(n)) --> (x0 * y0)`;;

let SEQ_NEG = `!x x0. x --> x0 <=> (\n. --(x n)) --> --x0`;;

let SEQ_INV = `!x x0. x --> x0 /\ ~(x0 = &0) ==> (\n. inv(x n)) --> inv x0`;;

let SEQ_SUB = `!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) - y(n)) --> (x0 - y0)`;;

let SEQ_DIV = `!x x0 y y0. x --> x0 /\ y --> y0 /\ ~(y0 = &0) ==>
                  (\n. x(n) / y(n)) --> (x0 / y0)`;;

let SEQ_UNIQ = `!x x1 x2. x --> x1 /\ x --> x2 ==> (x1 = x2)`;;

let SEQ_NULL = `!s l. s --> l <=> (\n. s(n) - l) --> &0`;;

let SEQ_SUM = `!f l m n.
      (!r. m <= r /\ r < m + n ==> f r --> l r)
      ==> (\k. sum(m,n) (\r. f r k)) --> sum(m,n) l`;;

let SEQ_TRANSFORM = `!s t l N. (!n. N <= n ==> (s n = t n)) /\ s --> l ==> t --> l`;;

(*----------------------------------------------------------------------------*)
(* Define convergence and Cauchy-ness                                         *)
(*----------------------------------------------------------------------------*)

let convergent = new_definition(
  `convergent f <=> ?l. f --> l`);;

let cauchy = new_definition(
  `cauchy f <=> !e. &0 < e ==>
        ?N:num. !m n. m >= N /\ n >= N ==> abs(f(m) - f(n)) < e`);;

let lim = new_definition(
  `lim f = @l. f --> l`);;

let SEQ_LIM = `!f. convergent f <=> (f --> lim f)`;;

(*----------------------------------------------------------------------------*)
(* Define a subsequence                                                       *)
(*----------------------------------------------------------------------------*)

let subseq = new_definition(
  `subseq (f:num->num) <=> !m n. m < n ==> (f m) < (f n)`);;

let SUBSEQ_SUC = `!f. subseq f <=> !n. f(n) < f(SUC n)`;;

(*----------------------------------------------------------------------------*)
(* Define monotonicity                                                        *)
(*----------------------------------------------------------------------------*)

let mono = new_definition(
  `mono (f:num->real) <=>
            (!m n. m <= n ==> f(m) <= f(n)) \/
            (!m n. m <= n ==> f(m) >= f(n))`);;

let MONO_SUC = `!f. mono f <=> (!n. f(SUC n) >= f(n)) \/ (!n. f(SUC n) <= f(n))`;;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of bounded sequence                               *)
(*----------------------------------------------------------------------------*)

let MAX_LEMMA = `!s N. ?k. !n:num. n < N ==> abs(s n) < k`;;

let SEQ_BOUNDED = `!s. bounded(mr1, (>=)) s <=> ?k. !n:num. abs(s n) < k`;;

let SEQ_BOUNDED_2 = `!f k K. (!n:num. k <= f(n) /\ f(n) <= K) ==> bounded(mr1, (>=)) f`;;

(*----------------------------------------------------------------------------*)
(* Show that every Cauchy sequence is bounded                                 *)
(*----------------------------------------------------------------------------*)

let SEQ_CBOUNDED = `!f. cauchy f ==> bounded(mr1, (>=)) f`;;

(*----------------------------------------------------------------------------*)
(* Show that a bounded and monotonic sequence converges                       *)
(*----------------------------------------------------------------------------*)

let SEQ_ICONV = `!f. bounded(mr1, (>=)) f /\ (!m n. m >= n ==> f(m) >= f(n))
           ==> convergent f`;;

let SEQ_NEG_CONV = `!f. convergent f <=> convergent (\n. --(f n))`;;

let SEQ_NEG_BOUNDED = `!f. bounded(mr1, (>=))(\n:num. --(f n)) <=> bounded(mr1, (>=)) f`;;

let SEQ_BCONV = `!f. bounded(mr1, (>=)) f /\ mono f ==> convergent f`;;

(*----------------------------------------------------------------------------*)
(* Show that every sequence contains a monotonic subsequence                  *)
(*----------------------------------------------------------------------------*)

let SEQ_MONOSUB = `!s:num->real. ?f. subseq f /\ mono(\n.s(f n))`;;

(*----------------------------------------------------------------------------*)
(* Show that a subsequence of a bounded sequence is bounded                   *)
(*----------------------------------------------------------------------------*)

let SEQ_SBOUNDED = `!s (f:num->num). bounded(mr1, (>=)) s ==> bounded(mr1, (>=)) (\n. s(f n))`;;

(*----------------------------------------------------------------------------*)
(* Show we can take subsequential terms arbitrarily far up a sequence         *)
(*----------------------------------------------------------------------------*)

let SEQ_SUBLE = `!f n. subseq f ==> n <= f(n)`;;

let SEQ_DIRECT = `!f. subseq f ==> !N1 N2. ?n. n >= N1 /\ f(n) >= N2`;;

(*----------------------------------------------------------------------------*)
(* Now show that every Cauchy sequence converges                              *)
(*----------------------------------------------------------------------------*)

let SEQ_CAUCHY = `!f. cauchy f <=> convergent f`;;

(*----------------------------------------------------------------------------*)
(* The limit comparison property for sequences                                *)
(*----------------------------------------------------------------------------*)

let SEQ_LE = `!f g l m. f --> l /\ g --> m /\ (?N. !n. n >= N ==> f(n) <= g(n))
        ==> l <= m`;;

(* ------------------------------------------------------------------------- *)
(* When a sequence tends to zero.                                            *)
(* ------------------------------------------------------------------------- *)

let SEQ_LE_0 = `!f g. f --> &0 /\ (?N. !n. n >= N ==> abs(g n) <= abs(f n))
         ==> g --> &0`;;

(*----------------------------------------------------------------------------*)
(* We can displace a convergent series by 1                                   *)
(*----------------------------------------------------------------------------*)

let SEQ_SUC = `!f l. f --> l <=> (\n. f(SUC n)) --> l`;;

(*----------------------------------------------------------------------------*)
(* Prove a sequence tends to zero iff its abs does                            *)
(*----------------------------------------------------------------------------*)

let SEQ_ABS = `!f. (\n. abs(f n)) --> &0 <=> f --> &0`;;

(*----------------------------------------------------------------------------*)
(* Half this is true for a general limit                                      *)
(*----------------------------------------------------------------------------*)

let SEQ_ABS_IMP = `!f l. f --> l ==> (\n. abs(f n)) --> abs(l)`;;

(*----------------------------------------------------------------------------*)
(* Prove that an unbounded sequence's inverse tends to 0                      *)
(*----------------------------------------------------------------------------*)

let SEQ_INV0 = `!f. (!y. ?N. !n. n >= N ==> f(n) > y)
        ==> (\n. inv(f n)) --> &0`;;

(*----------------------------------------------------------------------------*)
(* Important limit of c^n for |c| < 1                                         *)
(*----------------------------------------------------------------------------*)

let SEQ_POWER_ABS = `!c. abs(c) < &1 ==> (\n. abs(c) pow n) --> &0`;;

(*----------------------------------------------------------------------------*)
(* Similar version without the abs                                            *)
(*----------------------------------------------------------------------------*)

let SEQ_POWER = `!c. abs(c) < &1 ==> (\n. c pow n) --> &0`;;

(* ------------------------------------------------------------------------- *)
(* Convergence to 0 of harmonic sequence (not series of course).             *)
(* ------------------------------------------------------------------------- *)

let SEQ_HARMONIC = `!a. (\n. a / &n) --> &0`;;

(* ------------------------------------------------------------------------- *)
(* Other basic lemmas about sequences.                                       *)
(* ------------------------------------------------------------------------- *)

let SEQ_SUBSEQ = `!f l. f --> l ==> !a b. ~(a = 0) ==> (\n. f(a * n + b)) --> l`;;

let SEQ_POW = `!f l. (f --> l) ==> !n. (\i. f(i) pow n) --> l pow n`;;

(*----------------------------------------------------------------------------*)
(* Useful lemmas about nested intervals and proof by bisection                *)
(*----------------------------------------------------------------------------*)

let NEST_LEMMA = `!f g. (!n. f(SUC n) >= f(n)) /\
         (!n. g(SUC n) <= g(n)) /\
         (!n. f(n) <= g(n)) ==>
                ?l m. l <= m /\ ((!n. f(n) <= l) /\ f --> l) /\
                                ((!n. m <= g(n)) /\ g --> m)`;;

let NEST_LEMMA_UNIQ = `!f g. (!n. f(SUC n) >= f(n)) /\
         (!n. g(SUC n) <= g(n)) /\
         (!n. f(n) <= g(n)) /\
         (\n. f(n) - g(n)) --> &0 ==>
                ?l. ((!n. f(n) <= l) /\ f --> l) /\
                    ((!n. l <= g(n)) /\ g --> l)`;;

let BOLZANO_LEMMA = `!P. (!a b c. a <= b /\ b <= c /\ P(a,b) /\ P(b,c) ==> P(a,c)) /\
       (!x. ?d. &0 < d /\ !a b. a <= x /\ x <= b /\ (b - a) < d ==> P(a,b))
      ==> !a b. a <= b ==> P(a,b)`;;

(* ------------------------------------------------------------------------- *)
(* This one is better for higher-order matching.                             *)
(* ------------------------------------------------------------------------- *)

let BOLZANO_LEMMA_ALT = `!P. (!a b c. a <= b /\ b <= c /\ P a b /\ P b c ==> P a c) /\
       (!x. ?d. &0 < d /\ (!a b. a <= x /\ x <= b /\ b - a < d ==> P a b))
       ==> !a b. a <= b ==> P a b`;;

(*----------------------------------------------------------------------------*)
(* Define infinite sums                                                       *)
(*----------------------------------------------------------------------------*)

let sums = new_definition
  `f sums s <=> (\n. sum(0,n) f) --> s`;;

let summable = new_definition(
  `summable f <=> ?s. f sums s`);;

let suminf = new_definition(
  `suminf f = @s. f sums s`);;

(*----------------------------------------------------------------------------*)
(* If summable then it sums to the sum (!)                                    *)
(*----------------------------------------------------------------------------*)

let SUM_SUMMABLE = `!f l. f sums l ==> summable f`;;

let SUMMABLE_SUM = `!f. summable f ==> f sums (suminf f)`;;

(*----------------------------------------------------------------------------*)
(* And the sum is unique                                                      *)
(*----------------------------------------------------------------------------*)

let SUM_UNIQ = `!f x. f sums x ==> (x = suminf f)`;;

let SER_UNIQ = `!f x y. f sums x /\ f sums y ==> (x = y)`;;

(*----------------------------------------------------------------------------*)
(* Series which is zero beyond a certain point                                *)
(*----------------------------------------------------------------------------*)

let SER_0 = `!f n. (!m. n <= m ==> (f(m) = &0)) ==>
        f sums (sum(0,n) f)`;;

(*----------------------------------------------------------------------------*)
(* summable series of positive terms has limit >(=) any partial sum           *)
(*----------------------------------------------------------------------------*)

let SER_POS_LE = `!f n. summable f /\ (!m. n <= m ==> &0 <= f(m))
        ==> sum(0,n) f <= suminf f`;;

let SER_POS_LT = `!f n. summable f /\ (!m. n <= m ==> &0 < f(m))
        ==> sum(0,n) f < suminf f`;;

(*----------------------------------------------------------------------------*)
(* Theorems about grouping and offsetting, *not* permuting, terms             *)
(*----------------------------------------------------------------------------*)

let SER_GROUP = `!f k. summable f /\ 0 < k ==>
          (\n. sum(n * k,k) f) sums (suminf f)`;;

let SER_PAIR = `!f. summable f ==> (\n. sum(2 * n,2) f) sums (suminf f)`;;

let SER_OFFSET = `!f. summable f ==> !k. (\n. f(n + k)) sums (suminf f - sum(0,k) f)`;;

let SER_OFFSET_REV = `!f k. summable(\n. f(n + k)) ==>
         f sums (sum(0,k) f) + suminf (\n. f(n + k))`;;

(*----------------------------------------------------------------------------*)
(* Similar version for pairing up terms                                       *)
(*----------------------------------------------------------------------------*)

let SER_POS_LT_PAIR = `!f n. summable f /\
         (!d. &0 < (f(n + (2 * d))) +
               f(n + ((2 * d) + 1)))
        ==> sum(0,n) f < suminf f`;;

(*----------------------------------------------------------------------------*)
(* Prove a few composition formulas for series                                *)
(*----------------------------------------------------------------------------*)

let SER_ADD = `!x x0 y y0. x sums x0 /\ y sums y0 ==> (\n. x(n) + y(n)) sums (x0 + y0)`;;

let SER_CMUL = `!x x0 c. x sums x0 ==> (\n. c * x(n)) sums (c * x0)`;;

let SER_NEG = `!x x0. x sums x0 ==> (\n. --(x n)) sums --x0`;;

let SER_SUB = `!x x0 y y0. x sums x0 /\ y sums y0 ==> (\n. x(n) - y(n)) sums (x0 - y0)`;;

let SER_CDIV = `!x x0 c. x sums x0 ==> (\n. x(n) / c) sums (x0 / c)`;;

(*----------------------------------------------------------------------------*)
(* Prove Cauchy-type criterion for convergence of series                      *)
(*----------------------------------------------------------------------------*)

let SER_CAUCHY = `!f. summable f <=>
          !e. &0 < e ==> ?N. !m n. m >= N ==> abs(sum(m,n) f) < e`;;

(*----------------------------------------------------------------------------*)
(* Show that if a series converges, the terms tend to 0                       *)
(*----------------------------------------------------------------------------*)

let SER_ZERO = `!f. summable f ==> f --> &0`;;

(*----------------------------------------------------------------------------*)
(* Now prove the comparison test                                              *)
(*----------------------------------------------------------------------------*)

let SER_COMPAR = `!f g. (?N. !n. n >= N ==> abs(f(n)) <= g(n)) /\ summable g ==>
            summable f`;;

(*----------------------------------------------------------------------------*)
(* And a similar version for absolute convergence                             *)
(*----------------------------------------------------------------------------*)

let SER_COMPARA = `!f g. (?N. !n. n >= N ==> abs(f(n)) <= g(n)) /\ summable g ==>
            summable (\k. abs(f k))`;;

(*----------------------------------------------------------------------------*)
(* Limit comparison property for series                                       *)
(*----------------------------------------------------------------------------*)

let SER_LE = `!f g. (!n. f(n) <= g(n)) /\ summable f /\ summable g
        ==> suminf f <= suminf g`;;

let SER_LE2 = `!f g. (!n. abs(f n) <= g(n)) /\ summable g ==>
                summable f /\ suminf f <= suminf g`;;

(*----------------------------------------------------------------------------*)
(* Show that absolute convergence implies normal convergence                  *)
(*----------------------------------------------------------------------------*)

let SER_ACONV = `!f. summable (\n. abs(f n)) ==> summable f`;;

(*----------------------------------------------------------------------------*)
(* Absolute value of series                                                   *)
(*----------------------------------------------------------------------------*)

let SER_ABS = `!f. summable(\n. abs(f n)) ==> abs(suminf f) <= suminf(\n. abs(f n))`;;

(*----------------------------------------------------------------------------*)
(* Prove sum of geometric progression (useful for comparison)                 *)
(*----------------------------------------------------------------------------*)

let GP_FINITE = `!x. ~(x = &1) ==>
        !n. (sum(0,n) (\n. x pow n) = ((x pow n) - &1) / (x - &1))`;;

let GP = `!x. abs(x) < &1 ==> (\n. x pow n) sums inv(&1 - x)`;;

(*----------------------------------------------------------------------------*)
(* Now prove the ratio test                                                   *)
(*----------------------------------------------------------------------------*)

let ABS_NEG_LEMMA = `!c x y. c <= &0 ==> abs(x) <= c * abs(y) ==> (x = &0)`;;

let SER_RATIO = `!f c N. c < &1 /\
           (!n. n >= N ==> abs(f(SUC n)) <= c * abs(f(n))) ==>
       summable f`;;

(* ------------------------------------------------------------------------- *)
(* The error in truncating a convergent series is bounded by partial sums.   *)
(* ------------------------------------------------------------------------- *)

let SEQ_TRUNCATION = `!f l n b.
        f sums l /\ (!m. abs(sum(n,m) f) <= b)
        ==> abs(l - sum(0,n) f) <= b`;;

(*============================================================================*)
(* Theory of limits, continuity and differentiation of real->real functions   *)
(*============================================================================*)

parse_as_infix ("tends_real_real",(12,"right"));;

parse_as_infix ("diffl",(12,"right"));;
parse_as_infix ("contl",(12,"right"));;
parse_as_infix ("differentiable",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Specialize nets theorems to the pointwise limit of real->real functions    *)
(*----------------------------------------------------------------------------*)

let tends_real_real = new_definition
  `(f tends_real_real l)(x0) <=>
        (f tends l)(mtop(mr1),tendsto(mr1,x0))`;;

override_interface ("-->",`(tends_real_real)`);;

let LIM = `!f y0 x0. (f --> y0)(x0) <=>
        !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < abs(x - x0) /\ abs(x - x0) < d ==>
                abs(f(x) - y0) < e`;;

let LIM_CONST = `!k x. ((\x. k) --> k)(x)`;;

let LIM_ADD = `!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) + g(x)) --> (l + m))(x)`;;

let LIM_MUL = `!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) * g(x)) --> (l * m))(x)`;;

let LIM_NEG = `!f l. (f --> l)(x) <=> ((\x. --(f(x))) --> --l)(x)`;;

let LIM_INV = `!f l. (f --> l)(x) /\ ~(l = &0) ==>
        ((\x. inv(f(x))) --> inv l)(x)`;;

let LIM_SUB = `!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) - g(x)) --> (l - m))(x)`;;

let LIM_DIV = `!f g l m. (f --> l)(x) /\ (g --> m)(x) /\ ~(m = &0) ==>
      ((\x. f(x) / g(x)) --> (l / m))(x)`;;

let LIM_NULL = `!f l x. (f --> l)(x) <=> ((\x. f(x) - l) --> &0)(x)`;;

let LIM_SUM = `!f l m n x.
      (!r. m <= r /\ r < m + n ==> (f r --> l r)(x))
      ==> ((\x. sum(m,n) (\r. f r x)) --> sum(m,n) l)(x)`;;

(*----------------------------------------------------------------------------*)
(* One extra theorem is handy                                                 *)
(*----------------------------------------------------------------------------*)

let LIM_X = `!x0. ((\x. x) --> x0)(x0)`;;

(*----------------------------------------------------------------------------*)
(* Uniqueness of limit                                                        *)
(*----------------------------------------------------------------------------*)

let LIM_UNIQ = `!f l m x. (f --> l)(x) /\ (f --> m)(x) ==> (l = m)`;;

(*----------------------------------------------------------------------------*)
(* Show that limits are equal when functions are equal except at limit point  *)
(*----------------------------------------------------------------------------*)

let LIM_EQUAL = `!f g l x0. (!x. ~(x = x0) ==> (f x = g x)) ==>
        ((f --> l)(x0) <=> (g --> l)(x0))`;;

(*----------------------------------------------------------------------------*)
(* A more general theorem about rearranging the body of a limit               *)
(*----------------------------------------------------------------------------*)

let LIM_TRANSFORM = `!f g x0 l. ((\x. f(x) - g(x)) --> &0)(x0) /\ (g --> l)(x0)
        ==> (f --> l)(x0)`;;

(*----------------------------------------------------------------------------*)
(* Define differentiation and continuity                                      *)
(*----------------------------------------------------------------------------*)

let diffl = new_definition
  `(f diffl l)(x) <=> ((\h. (f(x+h) - f(x)) / h) --> l)(&0)`;;

let contl = new_definition
  `f contl x <=> ((\h. f(x + h)) --> f(x))(&0)`;;

let differentiable = new_definition
  `f differentiable x <=> ?l. (f diffl l)(x)`;;

(*----------------------------------------------------------------------------*)
(* Derivative is unique                                                       *)
(*----------------------------------------------------------------------------*)

let DIFF_UNIQ = `!f l m x. (f diffl l)(x) /\ (f diffl m)(x) ==> (l = m)`;;

(*----------------------------------------------------------------------------*)
(* Differentiability implies continuity                                       *)
(*----------------------------------------------------------------------------*)

let DIFF_CONT = `!f l x. (f diffl l)(x) ==> f contl x`;;

(*----------------------------------------------------------------------------*)
(* Alternative definition of continuity                                       *)
(*----------------------------------------------------------------------------*)

let CONTL_LIM = `!f x. f contl x <=> (f --> f(x))(x)`;;

(*----------------------------------------------------------------------------*)
(* Simple combining theorems for continuity                                   *)
(*----------------------------------------------------------------------------*)

let CONT_X = `!x. (\x. x) contl x`;;

let CONT_CONST = `!x. (\x. k) contl x`;;

let CONT_ADD = `!x. f contl x /\ g contl x ==> (\x. f(x) + g(x)) contl x`;;

let CONT_MUL = `!x. f contl x /\ g contl x ==> (\x. f(x) * g(x)) contl x`;;

let CONT_NEG = `!x. f contl x ==> (\x. --(f(x))) contl x`;;

let CONT_INV = `!x. f contl x /\ ~(f x = &0) ==> (\x. inv(f(x))) contl x`;;

let CONT_SUB = `!x. f contl x /\ g contl x ==> (\x. f(x) - g(x)) contl x`;;

let CONT_DIV = `!x. f contl x /\ g contl x /\ ~(g x = &0) ==>
        (\x. f(x) / g(x)) contl x`;;

let CONT_ABS = `!f x. f contl x ==> (\x. abs(f x)) contl x`;;

(* ------------------------------------------------------------------------- *)
(* Composition of continuous functions is continuous.                        *)
(* ------------------------------------------------------------------------- *)

let CONT_COMPOSE = `!f g x. f contl x /\ g contl (f x) ==> (\x. g(f x)) contl x`;;

(*----------------------------------------------------------------------------*)
(* Intermediate Value Theorem (we prove contrapositive by bisection)          *)
(*----------------------------------------------------------------------------*)

let IVT = `!f a b y. a <= b /\
             (f(a) <= y /\ y <= f(b)) /\
             (!x. a <= x /\ x <= b ==> f contl x)
        ==> (?x. a <= x /\ x <= b /\ (f(x) = y))`;;

(*----------------------------------------------------------------------------*)
(* Intermediate value theorem where value at the left end is bigger           *)
(*----------------------------------------------------------------------------*)

let IVT2 = `!f a b y. (a <= b) /\ (f(b) <= y /\ y <= f(a)) /\
             (!x. a <= x /\ x <= b ==> f contl x) ==>
        ?x. a <= x /\ x <= b /\ (f(x) = y)`;;

(*----------------------------------------------------------------------------*)
(* Prove the simple combining theorems for differentiation                    *)
(*----------------------------------------------------------------------------*)

let DIFF_CONST = `!k x. ((\x. k) diffl &0)(x)`;;

let DIFF_ADD = `!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)`;;

let DIFF_MUL = `!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                  ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)`;;

let DIFF_CMUL = `!f c l x. (f diffl l)(x) ==> ((\x. c * f(x)) diffl (c * l))(x)`;;

let DIFF_NEG = `!f l x. (f diffl l)(x) ==> ((\x. --(f x)) diffl --l)(x)`;;

let DIFF_SUB = `!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)`;;

(* ------------------------------------------------------------------------- *)
(* Carathe'odory definition makes the chain rule proof much easier.          *)
(* ------------------------------------------------------------------------- *)

let DIFF_CARAT = `!f l x. (f diffl l)(x) <=>
      ?g. (!z. f(z) - f(x) = g(z) * (z - x)) /\ g contl x /\ (g(x) = l)`;;

(*----------------------------------------------------------------------------*)
(* Now the chain rule                                                         *)
(*----------------------------------------------------------------------------*)

let DIFF_CHAIN = `!f g l m x.
     (f diffl l)(g x) /\ (g diffl m)(x) ==> ((\x. f(g x)) diffl (l * m))(x)`;;

(*----------------------------------------------------------------------------*)
(* Differentiation of natural number powers                                   *)
(*----------------------------------------------------------------------------*)

let DIFF_X = `!x. ((\x. x) diffl &1)(x)`;;

let DIFF_POW = `!n x. ((\x. x pow n) diffl (&n * (x pow (n - 1))))(x)`;;

(*----------------------------------------------------------------------------*)
(* Now power of -1 (then differentiation of inverses follows from chain rule) *)
(*----------------------------------------------------------------------------*)

let DIFF_XM1 = `!x. ~(x = &0) ==> ((\x. inv(x)) diffl (--(inv(x) pow 2)))(x)`;;

(*----------------------------------------------------------------------------*)
(* Now differentiation of inverse and quotient                                *)
(*----------------------------------------------------------------------------*)

let DIFF_INV = `!f l x. (f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl --(l / (f(x) pow 2)))(x)`;;

let DIFF_DIV = `!f g l m. (f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)`;;

(*----------------------------------------------------------------------------*)
(* Differentiation of finite sum                                              *)
(*----------------------------------------------------------------------------*)

let DIFF_SUM = `!f f' m n x. (!r. m <= r /\ r < (m + n)
                 ==> ((\x. f r x) diffl (f' r x))(x))
     ==> ((\x. sum(m,n)(\n. f n x)) diffl (sum(m,n) (\r. f' r x)))(x)`;;

(*----------------------------------------------------------------------------*)
(* By bisection, function continuous on closed interval is bounded above      *)
(*----------------------------------------------------------------------------*)

let CONT_BOUNDED = `!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. !x. a <= x /\ x <= b ==> f(x) <= M`;;

let CONT_BOUNDED_ABS = `!f a b. (!x. a <= x /\ x <= b ==> f contl x)
           ==> ?M. !x. a <= x /\ x <= b ==> abs(f(x)) <= M`;;

(*----------------------------------------------------------------------------*)
(* Refine the above to existence of least upper bound                         *)
(*----------------------------------------------------------------------------*)

let CONT_HASSUP = `!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (!N. N < M ==> ?x. a <= x /\ x <= b /\ N < f(x))`;;

(*----------------------------------------------------------------------------*)
(* Now show that it attains its upper bound                                   *)
(*----------------------------------------------------------------------------*)

let CONT_ATTAINS = `!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))`;;

(*----------------------------------------------------------------------------*)
(* Same theorem for lower bound                                               *)
(*----------------------------------------------------------------------------*)

let CONT_ATTAINS2 = `!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> M <= f(x)) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))`;;

(* ------------------------------------------------------------------------- *)
(* Another version.                                                          *)
(* ------------------------------------------------------------------------- *)

let CONT_ATTAINS_ALL = `!f a b. (a <= b /\ !x. a <= x /\ x <= b ==>  f contl x)
        ==> ?L M. (!x. a <= x /\ x <= b ==> L <= f(x) /\ f(x) <= M) /\
                  !y. L <= y /\ y <= M ==> ?x. a <= x /\ x <= b /\ (f(x) = y)`;;

(*----------------------------------------------------------------------------*)
(* If f'(x) > 0 then x is locally strictly increasing at the right            *)
(*----------------------------------------------------------------------------*)

let DIFF_LINC = `!f x l. (f diffl l)(x) /\ &0 < l ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x + h)`;;

(*----------------------------------------------------------------------------*)
(* If f'(x) < 0 then x is locally strictly increasing at the left             *)
(*----------------------------------------------------------------------------*)

let DIFF_LDEC = `!f x l. (f diffl l)(x) /\ l < &0 ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x - h)`;;

(*----------------------------------------------------------------------------*)
(* If f is differentiable at a local maximum x, f'(x) = 0                     *)
(*----------------------------------------------------------------------------*)

let DIFF_LMAX = `!f x l. (f diffl l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(y) <= f(x))) ==> (l = &0)`;;

(*----------------------------------------------------------------------------*)
(* Similar theorem for a local minimum                                        *)
(*----------------------------------------------------------------------------*)

let DIFF_LMIN = `!f x l. (f diffl l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(x) <= f(y))) ==> (l = &0)`;;

(*----------------------------------------------------------------------------*)
(* In particular if a function is locally flat                                *)
(*----------------------------------------------------------------------------*)

let DIFF_LCONST = `!f x l. (f diffl l)(x) /\
         (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x)))) ==> (l = &0)`;;

(*----------------------------------------------------------------------------*)
(* Lemma about introducing open ball in open interval                         *)
(*----------------------------------------------------------------------------*)

let INTERVAL_LEMMA_LT = `!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a < y /\ y < b`;;

let INTERVAL_LEMMA = `!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a <= y /\ y <= b`;;

(*----------------------------------------------------------------------------*)
(* Now Rolle's theorem                                                        *)
(*----------------------------------------------------------------------------*)

let ROLLE = `!f a b. a < b /\
           (f(a) = f(b)) /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?z. a < z /\ z < b /\ (f diffl &0)(z)`;;

(*----------------------------------------------------------------------------*)
(* Mean value theorem                                                         *)
(*----------------------------------------------------------------------------*)

let MVT_LEMMA = `!(f:real->real) a b.
        (\x. f(x) - (((f(b) - f(a)) / (b - a)) * x))(a) =
        (\x. f(x) - (((f(b) - f(a)) / (b - a)) * x))(b)`;;

let MVT = `!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?l z. a < z /\ z < b /\ (f diffl l)(z) /\
            (f(b) - f(a) = (b - a) * l)`;;

(* ------------------------------------------------------------------------- *)
(* Simple version with pure differentiability assumption.                    *)
(* ------------------------------------------------------------------------- *)

let MVT_ALT = `!f f' a b.
        a < b /\ (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x))
        ==> ?z. a < z /\ z < b /\ (f b - f a = (b - a) * f'(z))`;;

(*----------------------------------------------------------------------------*)
(* Theorem that function is constant if its derivative is 0 over an interval. *)
(*                                                                            *)
(* We could have proved this directly by bisection; consider instantiating    *)
(* BOLZANO_LEMMA with                                                         *)
(*                                                                            *)
(*     \(x,y). f(y) - f(x) <= C * (y - x)                                     *)
(*                                                                            *)
(* However the Rolle and Mean Value theorems are useful to have anyway        *)
(*----------------------------------------------------------------------------*)

let DIFF_ISCONST_END = `!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> (f b = f a)`;;

let DIFF_ISCONST = `!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> !x. a <= x /\ x <= b ==> (f x = f a)`;;

let DIFF_ISCONST_END_SIMPLE = `!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> (f diffl &0)(x))
        ==> (f b = f a)`;;

let DIFF_ISCONST_ALL = `!f x y. (!x. (f diffl &0)(x)) ==> (f(x) = f(y))`;;

(* ------------------------------------------------------------------------ *)
(* Boring lemma about distances                                             *)
(* ------------------------------------------------------------------------ *)

let INTERVAL_ABS = REAL_ARITH
  `!x z d. (x - d) <= z /\ z <= (x + d) <=> abs(z - x) <= d`;;

(* ------------------------------------------------------------------------ *)
(* Dull lemma that an continuous injection on an interval must have a strict*)
(* maximum at an end point, not in the middle.                              *)
(* ------------------------------------------------------------------------ *)

let CONT_INJ_LEMMA = `!f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(z) <= f(x))`;;

(* ------------------------------------------------------------------------ *)
(* Similar version for lower bound                                          *)
(* ------------------------------------------------------------------------ *)

let CONT_INJ_LEMMA2 = `!f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(x) <= f(z))`;;

(* ------------------------------------------------------------------------ *)
(* Show there's an interval surrounding f(x) in f[[x - d, x + d]]           *)
(* ------------------------------------------------------------------------ *)

let CONT_INJ_RANGE = `!f g x d.  &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
        ?e. &0 < e /\
            (!y. abs(y - f(x)) <= e ==> ?z. abs(z - x) <= d /\ (f z = y))`;;

(* ------------------------------------------------------------------------ *)
(* Continuity of inverse function                                           *)
(* ------------------------------------------------------------------------ *)

let CONT_INVERSE = `!f g x d. &0 < d /\
             (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
             (!z. abs(z - x) <= d ==> f contl z)
        ==> g contl (f x)`;;

(* ------------------------------------------------------------------------ *)
(* Differentiability of inverse function                                    *)
(* ------------------------------------------------------------------------ *)

let DIFF_INVERSE = `!f g l x d. &0 < d /\
               (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) <= d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)`;;

let DIFF_INVERSE_LT = `!f g l x d. &0 < d /\
               (!z. abs(z - x) < d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) < d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)`;;

(* ------------------------------------------------------------------------- *)
(* Every derivative is Darboux continuous.                                   *)
(* ------------------------------------------------------------------------- *)

let IVT_DERIVATIVE_0 = `!f f' a b.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) > &0 /\ f'(b) < &0
        ==> ?z. a < z /\ z < b /\ (f'(z) = &0)`;;

let IVT_DERIVATIVE_POS = `!f f' a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) > y /\ f'(b) < y
        ==> ?z. a < z /\ z < b /\ (f'(z) = y)`;;

let IVT_DERIVATIVE_NEG = `!f f' a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) < y /\ f'(b) > y
        ==> ?z. a < z /\ z < b /\ (f'(z) = y)`;;

(* ------------------------------------------------------------------------- *)
(* Uniformly convergent sequence of continuous functions is continuous.      *)
(* (Continuity at a point; uniformity in some neighbourhood of that point.)  *)
(* ------------------------------------------------------------------------- *)

let SEQ_CONT_UNIFORM = `!s f x0. (!e. &0 < e
                 ==> ?N d. &0 < d /\
                           !x n. abs(x - x0) < d /\ n >= N
                                 ==> abs(s n x - f(x)) < e) /\
            (?N:num. !n. n >= N ==> (s n) contl x0)
            ==> f contl x0`;;

(* ------------------------------------------------------------------------- *)
(* Comparison test gives uniform convergence of sum in a neighbourhood.      *)
(* ------------------------------------------------------------------------- *)

let SER_COMPARA_UNIFORM = `!s x0 g.
        (?N d. &0 < d /\
               !n x. abs(x - x0) < d /\ n >= N
                     ==> abs(s x n) <= g n) /\ summable g
        ==> ?f d. &0 < d /\
                  !e. &0 < e
                      ==> ?N. !x n. abs(x - x0) < d /\ n >= N
                                    ==> abs(sum(0,n) (s x) - f(x)) < e`;;

(* ------------------------------------------------------------------------- *)
(* A weaker variant matching the requirement for continuity of limit.        *)
(* ------------------------------------------------------------------------- *)

let SER_COMPARA_UNIFORM_WEAK = `!s x0 g.
        (?N d. &0 < d /\
               !n x. abs(x - x0) < d /\ n >= N
                     ==> abs(s x n) <= g n) /\ summable g
        ==> ?f. !e. &0 < e
                    ==> ?N d. &0 < d /\
                              !x n. abs(x - x0) < d /\ n >= N
                                    ==> abs(sum(0,n) (s x) - f(x)) < e`;;

(* ------------------------------------------------------------------------- *)
(* More convenient formulation of continuity.                                *)
(* ------------------------------------------------------------------------- *)

let CONTL = `!f x. f contl x <=>
         !e. &0 < e ==> ?d. &0 < d /\ !x'. abs(x' - x) < d
                            ==> abs(f(x') - f(x)) < e`;;

(* ------------------------------------------------------------------------- *)
(* Of course we also have this and similar results for sequences.            *)
(* ------------------------------------------------------------------------- *)

let CONTL_SEQ = `!f x l. f contl l /\ x tends_num_real l

           ==> (\n. f(x n)) tends_num_real f(l)`;;

(* ------------------------------------------------------------------------- *)
(* Uniformity of continuity over closed interval.                            *)
(* ------------------------------------------------------------------------- *)

let SUP_INTERVAL = `!P a b.
        (?x. a <= x /\ x <= b /\ P x)
        ==> ?s. a <= s /\ s <= b /\
                !y. y < s <=> (?x. a <= x /\ x <= b /\ P x /\ y < x)`;;

let CONT_UNIFORM = `!f a b. a <= b /\ (!x. a <= x /\ x <= b ==> f contl x)
           ==> !e. &0 < e ==> ?d. &0 < d /\
                                  !x y. a <= x /\ x <= b /\
                                        a <= y /\ y <= b /\
                                        abs(x - y) < d
                                        ==> abs(f(x) - f(y)) < e`;;

(* ------------------------------------------------------------------------- *)
(* Slightly stronger version exploiting 2-sided continuity at ends.          *)
(* ------------------------------------------------------------------------- *)

let CONT_UNIFORM_STRONG = `!f a b. (!x. a <= x /\ x <= b ==> f contl x)
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !x y. (a <= x /\ x <= b \/ a <= y /\ y <= b) /\
                                 abs(x - y) < d
                                 ==> abs(f(x) - f(y)) < e`;;

(* ------------------------------------------------------------------------- *)
(* Get rid of special syntax status of '-->'.                                *)
(* ------------------------------------------------------------------------- *)

remove_interface "-->";;
