(* ========================================================================= *)
(* Real vectors in Euclidean space, and elementary linear algebra.           *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*               (c) Copyright, Marco Maggesi 2014                           *)
(*       (c) Copyright, Andrea Gabrielli, Marco Maggesi 2016-2017            *)
(* ========================================================================= *)

needs "Library/matroids.ml";;
needs "Multivariate/misc.ml";;

(* ------------------------------------------------------------------------- *)
(* Some common special cases.                                                *)
(* ------------------------------------------------------------------------- *)

let FORALL_1 = `(!i. 1 <= i /\ i <= 1 ==> P i) <=> P 1`;;

let FORALL_2 = `!P. (!i. 1 <= i /\ i <= 2 ==> P i) <=> P 1 /\ P 2`;;

let FORALL_3 = `!P. (!i. 1 <= i /\ i <= 3 ==> P i) <=> P 1 /\ P 2 /\ P 3`;;

let FORALL_4 = `!P. (!i. 1 <= i /\ i <= 4 ==> P i) <=> P 1 /\ P 2 /\ P 3 /\ P 4`;;

let SUM_1 = `sum(1..1) f = f(1)`;;

let SUM_2 = `!t. sum(1..2) t = t(1) + t(2)`;;

let SUM_3 = `!t. sum(1..3) t = t(1) + t(2) + t(3)`;;

let SUM_4 = `!t. sum(1..4) t = t(1) + t(2) + t(3) + t(4)`;;

(* ------------------------------------------------------------------------- *)
(* Basic componentwise operations on vectors.                                *)
(* ------------------------------------------------------------------------- *)

let vector_add = new_definition
  `(vector_add:real^N->real^N->real^N) x y = lambda i. x$i + y$i`;;

let vector_sub = new_definition
  `(vector_sub:real^N->real^N->real^N) x y = lambda i. x$i - y$i`;;

let vector_neg = new_definition
  `(vector_neg:real^N->real^N) x = lambda i. --(x$i)`;;

overload_interface ("+",`(vector_add):real^N->real^N->real^N`);;
overload_interface ("-",`(vector_sub):real^N->real^N->real^N`);;
overload_interface ("--",`(vector_neg):real^N->real^N`);;

prioritize_real();;

let prioritize_vector = let ty = `:real^N` in
  fun () -> prioritize_overload ty;;

(* ------------------------------------------------------------------------- *)
(* Also the scalar-vector multiplication.                                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("%",(21,"right"));;

let vector_mul = new_definition
  `((%):real->real^N->real^N) c x = lambda i. c * x$i`;;

(* ------------------------------------------------------------------------- *)
(* Vectors corresponding to small naturals. Perhaps should overload "&"?     *)
(* ------------------------------------------------------------------------- *)

let vec = new_definition
  `(vec:num->real^N) n = lambda i. &n`;;

(* ------------------------------------------------------------------------- *)
(* Dot products.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("dot",(20,"right"));;

let dot = new_definition
  `(x:real^N) dot (y:real^N) = sum(1..dimindex(:N)) (\i. x$i * y$i)`;;

let DOT_1 = `(x:real^1) dot (y:real^1) = x$1 * y$1`;;

let DOT_2 = `(x:real^2) dot (y:real^2) = x$1 * y$1 + x$2 * y$2`;;

let DOT_3 = `(x:real^3) dot (y:real^3) = x$1 * y$1 + x$2 * y$2 + x$3 * y$3`;;

let DOT_4 = `(x:real^4) dot (y:real^4) = x$1 * y$1 + x$2 * y$2 + x$3 * y$3 + x$4 * y$4`;;

(* ------------------------------------------------------------------------- *)
(* A naive proof procedure to lift really trivial arithmetic stuff from R.   *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ARITH_TAC =
  let RENAMED_LAMBDA_BETA th =
    if fst(dest_fun_ty(type_of(funpow 3 rand (concl th)))) = aty
    then INST_TYPE [aty,bty; bty,aty] LAMBDA_BETA else LAMBDA_BETA in
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT(GEN_TAC ORELSE CONJ_TAC ORELSE DISCH_TAC ORELSE EQ_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[dot; GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG;
              GSYM SUM_LMUL; GSYM SUM_RMUL; GSYM SUM_NEG] THEN
  (MATCH_MP_TAC SUM_EQ_NUMSEG ORELSE MATCH_MP_TAC SUM_EQ_0_NUMSEG ORELSE
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [CART_EQ]) THEN
  REWRITE_TAC[AND_FORALL_THM] THEN TRY EQ_TAC THEN
  TRY(MATCH_MP_TAC MONO_FORALL) THEN GEN_TAC THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`;
              TAUT `(a ==> b) \/ (a ==> c) <=> a ==> b \/ c`] THEN
  TRY(MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`)) THEN
  REWRITE_TAC[vector_add; vector_sub; vector_neg; vector_mul; vec] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP(RENAMED_LAMBDA_BETA th) th]) THEN
  REAL_ARITH_TAC;;

let VECTOR_ARITH tm = prove(tm,VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Obvious "component-pushing".                                              *)
(* ------------------------------------------------------------------------- *)

let VEC_COMPONENT = `!k i. (vec k :real^N)$i = &k`;;

let VECTOR_ADD_COMPONENT = `!x:real^N y i. (x + y)$i = x$i + y$i`;;

let VECTOR_SUB_COMPONENT = `!x:real^N y i. (x - y)$i = x$i - y$i`;;

let VECTOR_NEG_COMPONENT = `!x:real^N i. (--x)$i = --(x$i)`;;

let VECTOR_MUL_COMPONENT = `!c x:real^N i. (c % x)$i = c * x$i`;;

let COND_COMPONENT = `(if b then x else y)$i = if b then x$i else y$i`;;

(* ------------------------------------------------------------------------- *)
(* Some frequently useful arithmetic lemmas over vectors.                    *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ADD_SYM = VECTOR_ARITH `!x y:real^N. x + y = y + x`;;

let VECTOR_ADD_LID = VECTOR_ARITH `!x. vec 0 + x = x`;;

let VECTOR_ADD_RID = VECTOR_ARITH `!x. x + vec 0 = x`;;

let VECTOR_SUB_REFL = VECTOR_ARITH `!x. x - x = vec 0`;;

let VECTOR_ADD_LINV = VECTOR_ARITH `!x. --x + x = vec 0`;;

let VECTOR_ADD_RINV = VECTOR_ARITH `!x. x + --x = vec 0`;;

let VECTOR_SUB_RADD = VECTOR_ARITH `!x y. x - (x + y) = --y:real^N`;;

let VECTOR_NEG_SUB = VECTOR_ARITH `!x:real^N y. --(x - y) = y - x`;;

let VECTOR_SUB_EQ = VECTOR_ARITH `!x y. (x - y = vec 0) <=> (x = y)`;;

let VECTOR_MUL_ASSOC = VECTOR_ARITH `!a b x. a % (b % x) = (a * b) % x`;;

let VECTOR_MUL_LID = VECTOR_ARITH `!x. &1 % x = x`;;

let VECTOR_MUL_LZERO = VECTOR_ARITH `!x. &0 % x = vec 0`;;

let VECTOR_SUB_ADD = VECTOR_ARITH `(x - y) + y = x:real^N`;;

let VECTOR_SUB_ADD2 = VECTOR_ARITH `y + (x - y) = x:real^N`;;

let VECTOR_ADD_LDISTRIB = VECTOR_ARITH `c % (x + y) = c % x + c % y`;;

let VECTOR_SUB_LDISTRIB = VECTOR_ARITH `c % (x - y) = c % x - c % y`;;

let VECTOR_ADD_RDISTRIB = VECTOR_ARITH `(a + b) % x = a % x + b % x`;;

let VECTOR_SUB_RDISTRIB = VECTOR_ARITH `(a - b) % x = a % x - b % x`;;

let VECTOR_ADD_SUB = VECTOR_ARITH `(x + y:real^N) - x = y`;;

let VECTOR_EQ_ADDR = VECTOR_ARITH `(x + y = x) <=> (y = vec 0)`;;

let VECTOR_SUB = VECTOR_ARITH `x - y = x + --(y:real^N)`;;

let VECTOR_SUB_RZERO = VECTOR_ARITH `x - vec 0 = x`;;

let VECTOR_MUL_RZERO = VECTOR_ARITH `c % vec 0 = vec 0`;;

let VECTOR_NEG_MINUS1 = VECTOR_ARITH `--x = (--(&1)) % x`;;

let VECTOR_ADD_ASSOC = VECTOR_ARITH `(x:real^N) + y + z = (x + y) + z`;;

let VECTOR_SUB_LZERO = VECTOR_ARITH `vec 0 - x = --x`;;

let VECTOR_NEG_NEG = VECTOR_ARITH `--(--(x:real^N)) = x`;;

let VECTOR_MUL_LNEG = VECTOR_ARITH `--c % x = --(c % x)`;;

let VECTOR_MUL_RNEG = VECTOR_ARITH `c % --x = --(c % x)`;;

let VECTOR_NEG_0 = VECTOR_ARITH `--(vec 0) = vec 0`;;

let VECTOR_NEG_EQ_0 = VECTOR_ARITH `--x = vec 0 <=> x = vec 0`;;

let VECTOR_EQ_NEG2 = VECTOR_ARITH `!x y:real^N. --x = --y <=> x = y`;;

let VECTOR_ADD_AC = VECTOR_ARITH
  `(m + n = n + m:real^N) /\
   ((m + n) + p = m + n + p) /\
   (m + n + p = n + m + p)`;;

let VEC_EQ = `!m n. (vec m = vec n) <=> (m = n)`;;

(* ------------------------------------------------------------------------- *)
(* Analogous theorems for set-sums.                                          *)
(* ------------------------------------------------------------------------- *)

let SUMS_SYM = `!s t:real^N->bool.
        {x + y | x IN s /\ y IN t} = {y + x | y IN t /\ x IN s}`;;

let SUMS_ASSOC = `!s t u:real^N->bool.
        {w + z | w IN {x + y | x IN s /\ y IN t} /\ z IN u} =
        {x + v | x IN s /\ v IN {y + z | y IN t /\ z IN u}}`;;

(* ------------------------------------------------------------------------- *)
(* Infinitude of Euclidean space.                                            *)
(* ------------------------------------------------------------------------- *)

let EUCLIDEAN_SPACE_INFINITE = `INFINITE(:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* Properties of the dot product.                                            *)
(* ------------------------------------------------------------------------- *)

let DOT_SYM = VECTOR_ARITH `!x y. x dot y = y dot x`;;

let DOT_LADD = VECTOR_ARITH `!x y z. (x + y) dot z = (x dot z) + (y dot z)`;;

let DOT_RADD = VECTOR_ARITH `!x y z. x dot (y + z) = (x dot y) + (x dot z)`;;

let DOT_LSUB = VECTOR_ARITH `!x y z. (x - y) dot z = (x dot z) - (y dot z)`;;

let DOT_RSUB = VECTOR_ARITH `!x y z. x dot (y - z) = (x dot y) - (x dot z)`;;

let DOT_LMUL = VECTOR_ARITH `!c x y. (c % x) dot y = c * (x dot y)`;;

let DOT_RMUL = VECTOR_ARITH `!c x y. x dot (c % y) = c * (x dot y)`;;

let DOT_LNEG = VECTOR_ARITH `!x y. (--x) dot y = --(x dot y)`;;

let DOT_RNEG = VECTOR_ARITH `!x y. x dot (--y) = --(x dot y)`;;

let DOT_LZERO = VECTOR_ARITH `!x. (vec 0) dot x = &0`;;

let DOT_RZERO = VECTOR_ARITH `!x. x dot (vec 0) = &0`;;

let DOT_POS_LE = `!x. &0 <= x dot x`;;

let DOT_EQ_0 = `!x:real^N. ((x dot x = &0) <=> (x = vec 0))`;;

let DOT_POS_LT = `!x. (&0 < x dot x) <=> ~(x = vec 0)`;;

let FORALL_DOT_EQ_0 = `(!y. (!x. x dot y = &0) <=> y = vec 0) /\
   (!x. (!y. x dot y = &0) <=> x = vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* Some trivial theorems about mapping R^n itself.                           *)
(* ------------------------------------------------------------------------- *)

let REFLECT_UNIV = `IMAGE (--) (:real^N) = (:real^N)`;;

let TRANSLATION_UNIV = `!a. IMAGE (\x. a + x) (:real^N) = (:real^N)`;;

let TRANSLATION_SUBSET_GALOIS_RIGHT = `!s t a:real^N.
    s SUBSET IMAGE (\x. a + x) t <=> IMAGE (\x. --a + x) s SUBSET t`;;

let TRANSLATION_SUBSET_GALOIS_LEFT = `!s t a:real^N.
     IMAGE (\x. a + x) s SUBSET t <=> s SUBSET IMAGE (\x. --a + x) t`;;

let TRANSLATION_GALOIS = `!s t a:real^N. s = IMAGE (\x. a + x) t <=> t = IMAGE (\x. --a + x) s`;;

let IN_TRANSLATION_GALOIS = `!s a b:real^N. b IN IMAGE (\x. a + x) s <=> (b - a) IN s`;;

let IN_TRANSLATION_GALOIS_ALT = `!s a b:real^N. (a + b) IN s <=> b IN IMAGE (\x. --a + x) s`;;

(* ------------------------------------------------------------------------- *)
(* Useful for the special cases of 1 dimension.                              *)
(* ------------------------------------------------------------------------- *)

let FORALL_DIMINDEX_1 = `(!i. 1 <= i /\ i <= dimindex(:1) ==> P i) <=> P 1`;;

(* ------------------------------------------------------------------------- *)
(* The collapse of the general concepts to the real line R^1.                *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ONE = `!x:real^1. x = lambda i. x$1`;;

let FORALL_REAL_ONE = `(!x:real^1. P x) <=> (!x. P(lambda i. x))`;;

(* ------------------------------------------------------------------------- *)
(* The usual Euclidean norm and metric on R^n.                               *)
(* ------------------------------------------------------------------------- *)

make_overloadable "norm" `:A->real`;;
overload_interface("norm",`vector_norm:real^N->real`);;

let vector_norm = new_definition
  `norm x = sqrt(x dot x)`;;

override_interface("dist",`distance:real^N#real^N->real`);;

let dist = new_definition
  `dist(x,y) = norm(x - y)`;;

let NORM_REAL = `!x:real^1. norm(x) = abs(x$1)`;;

let DIST_REAL = `!x:real^1 y. dist(x,y) = abs(x$1 - y$1)`;;

let NORM_0 = `norm(vec 0) = &0`;;

let NORM_POS_LE = `!x. &0 <= norm x`;;

let NORM_NEG = `!x. norm(--x) = norm x`;;

let NORM_SUB = `!x y. norm(x - y) = norm(y - x)`;;

let NORM_MUL = `!a x. norm(a % x) = abs(a) * norm x`;;

let NORM_EQ_0_DOT = `!x. (norm x = &0) <=> (x dot x = &0)`;;

let NORM_EQ_0 = `!x. (norm x = &0) <=> (x = vec 0)`;;

let NORM_POS_LT = `!x. &0 < norm x <=> ~(x = vec 0)`;;

let NORM_POW_2 = `!x. norm(x) pow 2 = x dot x`;;

let NORM_EQ_0_IMP = `!x. (norm x = &0) ==> (x = vec 0)`;;

let NORM_LE_0 = `!x. norm x <= &0 <=> (x = vec 0)`;;

let VECTOR_MUL_EQ_0 = `!a x. (a % x = vec 0) <=> (a = &0) \/ (x = vec 0)`;;

let VECTOR_MUL_LCANCEL = `!a x y. (a % x = a % y) <=> (a = &0) \/ (x = y)`;;

let VECTOR_MUL_RCANCEL = `!a b x. (a % x = b % x) <=> (a = b) \/ (x = vec 0)`;;

let VECTOR_MUL_LCANCEL_IMP = `!a x y. ~(a = &0) /\ (a % x = a % y) ==> (x = y)`;;

let VECTOR_MUL_RCANCEL_IMP = `!a b x. ~(x = vec 0) /\ (a % x = b % x) ==> (a = b)`;;

let NORM_CAUCHY_SCHWARZ = `!(x:real^N) y. x dot y <= norm(x) * norm(y)`;;

let NORM_CAUCHY_SCHWARZ_ABS = `!x:real^N y. abs(x dot y) <= norm(x) * norm(y)`;;

let REAL_ABS_NORM = `!x. abs(norm x) = norm x`;;

let NORM_CAUCHY_SCHWARZ_DIV = `!x:real^N y. abs((x dot y) / (norm x * norm y)) <= &1`;;

let NORM_TRIANGLE = `!x y. norm(x + y) <= norm(x) + norm(y)`;;

let NORM_TRIANGLE_SUB = `!x y:real^N. norm(x) <= norm(y) + norm(x - y)`;;

let NORM_TRIANGLE_LE = `!x y. norm(x) + norm(y) <= e ==> norm(x + y) <= e`;;

let NORM_TRIANGLE_LT = `!x y. norm(x) + norm(y) < e ==> norm(x + y) < e`;;

let COMPONENT_LE_NORM = `!x:real^N i. abs(x$i) <= norm x`;;

let NORM_BOUND_COMPONENT_LE = `!x:real^N e. norm(x) <= e
                ==> !i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) <= e`;;

let NORM_BOUND_COMPONENT_LT = `!x:real^N e. norm(x) < e
                ==> !i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) < e`;;

let NORM_LE_L1 = `!x:real^N. norm x <= sum(1..dimindex(:N)) (\i. abs(x$i))`;;

let REAL_ABS_SUB_NORM = `abs(norm(x) - norm(y)) <= norm(x - y)`;;

let NORM_LE = `!x y. norm(x) <= norm(y) <=> x dot x <= y dot y`;;

let NORM_LT = `!x y. norm(x) < norm(y) <=> x dot x < y dot y`;;

let NORM_EQ = `!x y. (norm x = norm y) <=> (x dot x = y dot y)`;;

let NORM_EQ_1 = `!x. norm(x) = &1 <=> x dot x = &1`;;

let NORM_LE_COMPONENTWISE = `!x:real^N y:real^N.
        (!i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) <= abs(y$i))
        ==> norm(x) <= norm(y)`;;

let NORM_EQ_COMPONENTWISE = `!x:real^N y:real^N.
        (!i. 1 <= i /\ i <= dimindex (:N) ==> abs(x$i) = abs(y$i))
        ==> norm x = norm y`;;

let L1_LE_NORM = `!x:real^N.
    sum(1..dimindex(:N)) (\i. abs(x$i)) <= sqrt(&(dimindex(:N))) * norm x`;;

let DIST_INCREASES_ONLINE = `!a b d. ~(d = vec 0)
           ==> dist(a,b + d) > dist(a,b) \/ dist(a,b - d) > dist(a,b)`;;

let NORM_INCREASES_ONLINE = `!a:real^N d. ~(d = vec 0)
                ==> norm(a + d) > norm(a) \/ norm(a - d) > norm(a)`;;

(* ------------------------------------------------------------------------- *)
(* Squaring equations and inequalities involving norms.                      *)
(* ------------------------------------------------------------------------- *)

let DOT_SQUARE_NORM = `!x. x dot x = norm(x) pow 2`;;

let NORM_EQ_SQUARE = `!x:real^N. norm(x) = a <=> &0 <= a /\ x dot x = a pow 2`;;

let NORM_LE_SQUARE = `!x:real^N. norm(x) <= a <=> &0 <= a /\ x dot x <= a pow 2`;;

let NORM_GE_SQUARE = `!x:real^N. norm(x) >= a <=> a <= &0 \/ x dot x >= a pow 2`;;

let NORM_LT_SQUARE = `!x:real^N. norm(x) < a <=> &0 < a /\ x dot x < a pow 2`;;

let NORM_GT_SQUARE = `!x:real^N. norm(x) > a <=> a < &0 \/ x dot x > a pow 2`;;

let NORM_LT_SQUARE_ALT = `!x:real^N. norm(x) < a <=> &0 <= a /\ x dot x < a pow 2`;;

(* ------------------------------------------------------------------------- *)
(* General linear decision procedure for normed spaces.                      *)
(* ------------------------------------------------------------------------- *)

let NORM_ARITH =
  let find_normedterms =
    let augment_norm b tm acc =
      match tm with
        Comb(Const("vector_norm",_),v) -> insert (b,v) acc
      | _ -> acc in
    let rec find_normedterms tm acc =
      match tm with
        Comb(Comb(Const("real_add",_),l),r) ->
            find_normedterms l (find_normedterms r acc)
      | Comb(Comb(Const("real_mul",_),c),n) ->
            if not (is_ratconst c) then acc else
            augment_norm (rat_of_term c >=/ num 0) n acc
      | _ -> augment_norm true tm acc in
    find_normedterms in
  let lincomb_neg t = mapf minus_num t in
  let lincomb_cmul c t = if c =/ num 0 then undefined else mapf (( */ ) c) t in
  let lincomb_add l r = combine (+/) (fun x -> x =/ num 0) l r in
  let lincomb_sub l r = lincomb_add l (lincomb_neg r) in
  let lincomb_eq l r = lincomb_sub l r = undefined in
  let rec vector_lincomb tm =
    match tm with
        Comb(Comb(Const("vector_add",_),l),r) ->
          lincomb_add (vector_lincomb l) (vector_lincomb r)
      | Comb(Comb(Const("vector_sub",_),l),r) ->
          lincomb_sub (vector_lincomb l) (vector_lincomb r)
      | Comb(Comb(Const("%",_),l),r) ->
          lincomb_cmul (rat_of_term l) (vector_lincomb r)
      | Comb(Const("vector_neg",_),t) ->
          lincomb_neg (vector_lincomb t)
      | Comb(Const("vec",_),n) when is_numeral n && dest_numeral n =/ num 0 ->
          undefined
      | _ -> (tm |=> num 1) in
  let vector_lincombs tms =
    itlist (fun t fns ->
                  if can (assoc t) fns then fns else
                  let f = vector_lincomb t in
                  try let _,f' = find (fun (_,f') -> lincomb_eq f f') fns in
                      (t,f')::fns
                  with Failure _ -> (t,f)::fns) tms [] in
  let rec replacenegnorms fn tm =
    match tm with
      Comb(Comb(Const("real_add",_),l),r) ->
          BINOP_CONV (replacenegnorms fn) tm
    | Comb(Comb(Const("real_mul",_),c),n) when rat_of_term c </ num 0 ->
          RAND_CONV fn tm
    | _ -> REFL tm in
  let flip v eq =
    if defined eq v then (v |-> minus_num(apply eq v)) eq else eq in
  let rec allsubsets s =
    match s with
      [] -> [[]]
    | (a::t) -> let res = allsubsets t in
                map (fun b -> a::b) res @ res in
  let evaluate env lin =
    foldr (fun x c s -> s +/ c */ apply env x) lin (num 0) in
  let rec solve (vs,eqs) =
    match (vs,eqs) with
      [],[] -> (0 |=> num 1)
    | _,eq::oeqs ->
          let v = hd(intersect vs (dom eq)) in
          let c = apply eq v in
          let vdef = lincomb_cmul (num(-1) // c) eq in
          let eliminate eqn =
            if not(defined eqn v) then eqn else
            lincomb_add (lincomb_cmul (apply eqn v) vdef) eqn in
          let soln = solve (subtract vs [v],map eliminate oeqs) in
          (v |-> evaluate soln (undefine v vdef)) soln in
  let rec combinations k l =
    if k = 0 then [[]] else
    match l with
      [] -> []
    | h::t -> map (fun c -> h::c) (combinations (k - 1) t) @
              combinations k t in
  let vertices vs eqs =
    let vertex cmb =
      let soln = solve(vs,cmb) in
      map (fun v -> tryapplyd soln v (num 0)) vs in
    let rawvs = mapfilter vertex (combinations (length vs) eqs) in
    let unset = filter (forall (fun c -> c >=/ num 0)) rawvs in
    itlist (insert' (forall2 (=/))) unset [] in
  let subsumes l m = forall2 (fun x y -> abs_num x <=/ abs_num y) l m in
  let rec subsume todo dun =
    match todo with
      [] -> dun
    | v::ovs -> let dun' = if exists (fun w -> subsumes w v) dun then dun
                           else v::(filter (fun w -> not(subsumes v w)) dun) in
                subsume ovs dun' in
  let NORM_CMUL_RULE =
    let MATCH_pth = (MATCH_MP o prove)
     (`!b x. b >= norm(x) ==> !c. abs(c) * b >= norm(c % x)`,
      SIMP_TAC[NORM_MUL; real_ge; REAL_LE_LMUL; REAL_ABS_POS]) in
    fun c th -> ISPEC(term_of_rat c) (MATCH_pth th) in
  let NORM_ADD_RULE =
    let MATCH_pth = (MATCH_MP o prove)
     (`!b1 b2 x1 x2. b1 >= norm(x1) /\ b2 >= norm(x2)
                     ==> b1 + b2 >= norm(x1 + x2)`,
      REWRITE_TAC[real_ge] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC NORM_TRIANGLE_LE THEN ASM_SIMP_TAC[REAL_LE_ADD2]) in
    fun th1 th2 -> MATCH_pth (CONJ th1 th2) in
  let INEQUALITY_CANON_RULE =
    CONV_RULE(LAND_CONV REAL_POLY_CONV) o
    CONV_RULE(LAND_CONV REAL_RAT_REDUCE_CONV) o
    GEN_REWRITE_RULE I [REAL_ARITH `s >= t <=> s - t >= &0`] in
  let NORM_CANON_CONV =
    let APPLY_pth1 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `x:real^N = &1 % x`]
    and APPLY_pth2 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `x - y:real^N = x + --y`]
    and APPLY_pth3 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `--x:real^N = -- &1 % x`]
    and APPLY_pth4 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `&0 % x:real^N = vec 0`;
      VECTOR_ARITH `c % vec 0:real^N = vec 0`]
    and APPLY_pth5 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `c % (d % x) = (c * d) % x`]
    and APPLY_pth6 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `c % (x + y) = c % x + c % y`]
    and APPLY_pth7 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `vec 0 + x = x`;
      VECTOR_ARITH `x + vec 0 = x`]
    and APPLY_pth8 =
     GEN_REWRITE_CONV I [VECTOR_ARITH `c % x + d % x = (c + d) % x`] THENC
     LAND_CONV REAL_RAT_ADD_CONV THENC
     GEN_REWRITE_CONV TRY_CONV [VECTOR_ARITH `&0 % x = vec 0`]
    and APPLY_pth9 =
     GEN_REWRITE_CONV I
      [VECTOR_ARITH `(c % x + z) + d % x = (c + d) % x + z`;
       VECTOR_ARITH `c % x + (d % x + z) = (c + d) % x + z`;
       VECTOR_ARITH `(c % x + w) + (d % x + z) = (c + d) % x + (w + z)`] THENC
     LAND_CONV(LAND_CONV REAL_RAT_ADD_CONV)
    and APPLY_ptha =
     GEN_REWRITE_CONV I [VECTOR_ARITH `&0 % x + y = y`]
    and APPLY_pthb =
     GEN_REWRITE_CONV I
      [VECTOR_ARITH `c % x + d % y = c % x + d % y`;
       VECTOR_ARITH `(c % x + z) + d % y = c % x + (z + d % y)`;
       VECTOR_ARITH `c % x + (d % y + z) = c % x + (d % y + z)`;
       VECTOR_ARITH `(c % x + w) + (d % y + z) = c % x + (w + (d % y + z))`]
    and APPLY_pthc =
     GEN_REWRITE_CONV I
      [VECTOR_ARITH `c % x + d % y = d % y + c % x`;
       VECTOR_ARITH `(c % x + z) + d % y = d % y + (c % x + z)`;
       VECTOR_ARITH `c % x + (d % y + z) = d % y + (c % x + z)`;
       VECTOR_ARITH `(c % x + w) + (d % y + z) = d % y + ((c % x + w) + z)`]
    and APPLY_pthd =
     GEN_REWRITE_CONV TRY_CONV
      [VECTOR_ARITH `x + vec 0 = x`] in
    let headvector tm =
      match tm with
        Comb(Comb(Const("vector_add",_),Comb(Comb(Const("%",_),l),v)),r) -> v
      | Comb(Comb(Const("%",_),l),v) -> v
      | _ -> failwith "headvector: non-canonical term" in
    let rec VECTOR_CMUL_CONV tm =
     ((APPLY_pth5 THENC LAND_CONV REAL_RAT_MUL_CONV) ORELSEC
      (APPLY_pth6 THENC BINOP_CONV VECTOR_CMUL_CONV)) tm
    and VECTOR_ADD_CONV tm =
      try APPLY_pth7 tm with Failure _ ->
      try APPLY_pth8 tm with Failure _ ->
      match tm with
        Comb(Comb(Const("vector_add",_),lt),rt) ->
          let l = headvector lt and r = headvector rt in
          if l < r then (APPLY_pthb THENC
                         RAND_CONV VECTOR_ADD_CONV THENC
                         APPLY_pthd) tm
          else if r < l then (APPLY_pthc THENC
                              RAND_CONV VECTOR_ADD_CONV THENC
                              APPLY_pthd) tm else
          (APPLY_pth9 THENC
            ((APPLY_ptha THENC VECTOR_ADD_CONV) ORELSEC
             RAND_CONV VECTOR_ADD_CONV THENC
             APPLY_pthd)) tm
      | _ -> REFL tm in
    let rec VECTOR_CANON_CONV tm =
      match tm with
        Comb(Comb(Const("vector_add",_),l),r) ->
          let lth = VECTOR_CANON_CONV l and rth = VECTOR_CANON_CONV r in
          let th = MK_COMB(AP_TERM (rator(rator tm)) lth,rth) in
          CONV_RULE (RAND_CONV VECTOR_ADD_CONV) th
      | Comb(Comb(Const("%",_),l),r) ->
          let rth = AP_TERM (rator tm) (VECTOR_CANON_CONV r) in
          CONV_RULE (RAND_CONV(APPLY_pth4 ORELSEC VECTOR_CMUL_CONV)) rth
      | Comb(Comb(Const("vector_sub",_),l),r) ->
          (APPLY_pth2 THENC VECTOR_CANON_CONV) tm
      | Comb(Const("vector_neg",_),t) ->
          (APPLY_pth3 THENC VECTOR_CANON_CONV) tm
      | Comb(Const("vec",_),n) when is_numeral n && dest_numeral n =/ num 0 ->
          REFL tm
      | _ -> APPLY_pth1 tm in
    fun tm ->
      match tm with
       Comb(Const("vector_norm",_),e) -> RAND_CONV VECTOR_CANON_CONV tm
      | _ -> failwith "NORM_CANON_CONV" in
  let REAL_VECTOR_COMBO_PROVER =
    let pth_zero = `norm(vec 0:real^N) = &0`;;

let NORM_ARITH_TAC = CONV_TAC NORM_ARITH;;

let ASM_NORM_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  NORM_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* There are no non-trivial homomorphisms R->R                               *)
(* ------------------------------------------------------------------------- *)

let HOMOMORPHISM_REAL_TO_REAL = `!f:real->real.
        (!x y. f(x + y) = f x + f y) /\ (!x y. f(x * y) = f x * f y) <=>
        (f = \x. &0) \/ (f = \x. x)`;;

(* ------------------------------------------------------------------------- *)
(* Dot product in terms of the norm rather than conversely.                  *)
(* ------------------------------------------------------------------------- *)

let DOT_NORM = `!x y. x dot y = (norm(x + y) pow 2 - norm(x) pow 2 - norm(y) pow 2) / &2`;;

let DOT_NORM_SUB = `!x y. x dot y = ((norm(x) pow 2 + norm(y) pow 2) - norm(x - y) pow 2) / &2`;;

(* ------------------------------------------------------------------------- *)
(* Equality of vectors in terms of dot products.                             *)
(* ------------------------------------------------------------------------- *)

let VECTOR_EQ = `!x y. (x = y) <=> (x dot x = x dot y) /\ (y dot y = x dot x)`;;

(* ------------------------------------------------------------------------- *)
(* Hence more metric properties.                                             *)
(* ------------------------------------------------------------------------- *)

let DIST_REFL = `!x. dist(x,x) = &0`;;

let DIST_SYM = `!x y. dist(x,y) = dist(y,x)`;;

let DIST_POS_LE = `!x y. &0 <= dist(x,y)`;;

let REAL_ABS_DIST = `!x y:real^N. abs(dist(x,y)) = dist(x,y)`;;

let DIST_TRIANGLE = `!x:real^N y z. dist(x,z) <= dist(x,y) + dist(y,z)`;;

let DIST_TRIANGLE_ALT = `!x y z. dist(y,z) <= dist(x,y) + dist(x,z)`;;

let DIST_EQ_0 = `!x y. (dist(x,y) = &0) <=> (x = y)`;;

let DIST_POS_LT = `!x y. ~(x = y) ==> &0 < dist(x,y)`;;

let DIST_NZ = `!x y. ~(x = y) <=> &0 < dist(x,y)`;;

let DIST_TRIANGLE_LE = `!x y z e. dist(x,z) + dist(y,z) <= e ==> dist(x,y) <= e`;;

let DIST_TRIANGLE_LT = `!x y z e. dist(x,z) + dist(y,z) < e ==> dist(x,y) < e`;;

let DIST_TRIANGLE_HALF_L = `!x1 x2 y. dist(x1,y) < e / &2 /\ dist(x2,y) < e / &2 ==> dist(x1,x2) < e`;;

let DIST_TRIANGLE_HALF_R = `!x1 x2 y. dist(y,x1) < e / &2 /\ dist(y,x2) < e / &2 ==> dist(x1,x2) < e`;;

let DIST_TRIANGLE_ADD = `!x x' y y'. dist(x + y,x' + y') <= dist(x,x') + dist(y,y')`;;

let DIST_MUL = `!x y c. dist(c % x,c % y) = abs(c) * dist(x,y)`;;

let DIST_TRIANGLE_ADD_HALF = `!x x' y y':real^N.
    dist(x,x') < e / &2 /\ dist(y,y') < e / &2 ==> dist(x + y,x' + y') < e`;;

let DIST_LE_0 = `!x y. dist(x,y) <= &0 <=> x = y`;;

let DIST_EQ = `!w x y z. dist(w,x) = dist(y,z) <=> dist(w,x) pow 2 = dist(y,z) pow 2`;;

let DIST_0 = `!x. dist(x,vec 0) = norm(x) /\ dist(vec 0,x) = norm(x)`;;

(* ------------------------------------------------------------------------- *)
(* Bounding distances between scaled versions of vectors.                    *)
(* ------------------------------------------------------------------------- *)

let DIST_RESCALE = `!a x y:real^N. norm(x) = norm(y) ==> dist(a % x,y) = dist(x,a % y)`;;

let DIST_DESCALE = `!a b x y:real^N.
        &0 <= a /\ &0 <= b /\ norm(x) = norm(y)
        ==> dist(a % x,b % y) >= min a b * dist(x,y)`;;

(* ------------------------------------------------------------------------- *)
(* Sums of vectors.                                                          *)
(* ------------------------------------------------------------------------- *)

let NEUTRAL_VECTOR_ADD = `neutral(+) = vec 0:real^N`;;

let MONOIDAL_VECTOR_ADD = `monoidal((+):real^N->real^N->real^N)`;;

let vsum = new_definition
  `(vsum:(A->bool)->(A->real^N)->real^N) s f = lambda i. sum s (\x. f(x)$i)`;;

let VSUM_CLAUSES = `(!f. vsum {} f = vec 0) /\
   (!x f s. FINITE s
            ==> (vsum (x INSERT s) f =
                 if x IN s then vsum s f else f(x) + vsum s f))`;;

let VSUM = `!f s. FINITE s ==> vsum s f = iterate (+) s f`;;

let VSUM_EQ_0 = `!f s. (!x:A. x IN s ==> (f(x) = vec 0)) ==> (vsum s f = vec 0)`;;

let VSUM_0 = `vsum s (\x. vec 0) = vec 0`;;

let VSUM_LMUL = `!f c s.  vsum s (\x. c % f(x)) = c % vsum s f`;;

let VSUM_RMUL = `!c s v. vsum s (\x. c x % v) = (sum s c) % v`;;

let VSUM_ADD = `!f g s. FINITE s ==> (vsum s (\x. f x + g x) = vsum s f + vsum s g)`;;

let VSUM_SUB = `!f g s. FINITE s ==> (vsum s (\x. f x - g x) = vsum s f - vsum s g)`;;

let VSUM_CONST = `!c s. FINITE s ==> (vsum s (\n. c) = &(CARD s) % c)`;;

let VSUM_COMPONENT = `!s f:A->real^N i. vsum s f$i = sum s (\x. f x$i)`;;

let VSUM_IMAGE = `!f g s. FINITE s /\ (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (vsum (IMAGE f s) g = vsum s (g o f))`;;

let VSUM_UNION = `!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (vsum (s UNION t) f = vsum s f + vsum t f)`;;

let VSUM_DIFF = `!f s t. FINITE s /\ t SUBSET s
           ==> (vsum (s DIFF t) f = vsum s f - vsum t f)`;;

let VSUM_DELETE = `!f s a. FINITE s /\ a IN s
           ==> vsum (s DELETE a) f = vsum s f - f a`;;

let VSUM_INCL_EXCL = `!s t (f:A->real^N).
        FINITE s /\ FINITE t
        ==> vsum s f + vsum t f = vsum (s UNION t) f + vsum (s INTER t) f`;;

let VSUM_NEG = `!f s. vsum s (\x. --f x) = --vsum s f`;;

let VSUM_EQ = `!f g s. (!x. x IN s ==> (f x = g x)) ==> (vsum s f = vsum s g)`;;

let VSUM_SUPERSET = `!f:A->real^N u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = vec 0))
        ==> (vsum v f = vsum u f)`;;

let VSUM_SUPPORT = `!f:A->real^N s. vsum {x | x IN s /\ ~(f x = vec 0)} f = vsum s f`;;

let VSUM_UNIV = `!f:A->real^N s.
     support (+) f (:A) SUBSET s ==> vsum s f = vsum (:A) f`;;

let VSUM_EQ_SUPERSET = `!f s t:A->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> f(x) = vec 0)
        ==> vsum s f = vsum t g`;;

let VSUM_UNION_RZERO = `!f:A->real^N u v.
        (!x. x IN v /\ ~(x IN u) ==> (f(x) = vec 0))
        ==> (vsum (u UNION v) f = vsum u f)`;;

let VSUM_UNION_LZERO = `!f:A->real^N u v.
        (!x. x IN u /\ ~(x IN v) ==> (f(x) = vec 0))
        ==> (vsum (u UNION v) f = vsum v f)`;;

let VSUM_RESTRICT = `!f s. vsum s (\x. if x IN s then f(x) else vec 0) = vsum s f`;;

let VSUM_RESTRICT_SET = `!P s f. vsum {x | x IN s /\ P x} f =
           vsum s (\x. if P x then f x else vec 0)`;;

let VSUM_CASES = `!s P f g. FINITE s
             ==> vsum s (\x:A. if P x then (f x):real^N else g x) =
                 vsum {x | x IN s /\ P x} f + vsum {x | x IN s /\ ~P x} g`;;

let VSUM_SING = `!f x. vsum {x} f = f(x)`;;

let VSUM_NORM = `!f s. FINITE s ==> norm(vsum s f) <= sum s (\x. norm(f x))`;;

let VSUM_NORM_LE = `!s f:A->real^N g.
        FINITE s /\ (!x. x IN s ==> norm(f x) <= g(x))
        ==> norm(vsum s f) <= sum s g`;;

let VSUM_NORM_TRIANGLE = `!s f b. FINITE s /\ sum s (\a. norm(f a)) <= b ==> norm(vsum s f) <= b`;;

let VSUM_NORM_BOUND = `!s f b. FINITE s /\ (!x:A. x IN s ==> norm(f(x)) <= b)
           ==> norm(vsum s f) <= &(CARD s) * b`;;

let VSUM_CLAUSES_NUMSEG = `(!m. vsum(m..0) f = if m = 0 then f(0) else vec 0) /\
   (!m n. vsum(m..SUC n) f = if m <= SUC n then vsum(m..n) f + f(SUC n)
                             else vsum(m..n) f)`;;

let VSUM_CLAUSES_RIGHT = `!f m n. 0 < n /\ m <= n ==> vsum(m..n) f = vsum(m..n-1) f + (f n):real^N`;;

let VSUM_CMUL_NUMSEG = `!f c m n. vsum (m..n) (\x. c % f x) = c % vsum (m..n) f`;;

let VSUM_EQ_NUMSEG = `!f g m n.
         (!x. m <= x /\ x <= n ==> (f x = g x))
         ==> (vsum(m .. n) f = vsum(m .. n) g)`;;

let VSUM_IMAGE_GEN = `!f:A->B g s.
        FINITE s
        ==> (vsum s g =
             vsum (IMAGE f s) (\y. vsum {x | x IN s /\ (f(x) = y)} g))`;;

let VSUM_GROUP = `!f:A->B g s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> vsum t (\y. vsum {x | x IN s /\ f(x) = y} g) = vsum s g`;;

let VSUM_GROUP_RELATION = `!R:A->B->bool g s t.
         FINITE s /\
         (!x. x IN s ==> ?!y. y IN t /\ R x y)
         ==> vsum t (\y. vsum {x | x IN s /\ R x y} g) = vsum s g`;;

let VSUM_VMUL = `!f v s. (sum s f) % v = vsum s (\x. f(x) % v)`;;

let VSUM_DELTA = `!s a. vsum s (\x. if x = a then b else vec 0) =
         if a IN s then b else vec 0`;;

let VSUM_ADD_NUMSEG = `!f g m n. vsum(m..n) (\i. f i + g i) = vsum(m..n) f + vsum(m..n) g`;;

let VSUM_SUB_NUMSEG = `!f g m n. vsum(m..n) (\i. f i - g i) = vsum(m..n) f - vsum(m..n) g`;;

let VSUM_ADD_SPLIT = `!f m n p.
       m <= n + 1 ==> vsum(m..n + p) f = vsum(m..n) f + vsum(n + 1..n + p) f`;;

let VSUM_VSUM_PRODUCT = `!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> vsum s (\i. vsum (t i) (x i)) =
            vsum {i,j | i IN s /\ j IN t i} (\(i,j). x i j)`;;

let VSUM_IMAGE_NONZERO = `!d:B->real^N i:A->B s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ i x = i y ==> d(i x) = vec 0)
    ==> vsum (IMAGE i s) d = vsum s (d o i)`;;

let VSUM_UNION_NONZERO = `!f s t. FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> f(x) = vec 0)
           ==> vsum (s UNION t) f = vsum s f + vsum t f`;;

let VSUM_UNIONS_NONZERO = `!f s. FINITE s /\ (!t:A->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> f x = vec 0)
         ==> vsum (UNIONS s) f = vsum s (\t. vsum t f)`;;

let VSUM_CLAUSES_LEFT = `!f m n. m <= n ==> vsum(m..n) f = f m + vsum(m + 1..n) f`;;

let VSUM_DIFFS = `!m n. vsum(m..n) (\k. f(k) - f(k + 1)) =
          if m <= n then f(m) - f(n + 1) else vec 0`;;

let VSUM_DIFFS_ALT = `!m n. vsum(m..n) (\k. f(k + 1) - f(k)) =
          if m <= n then f(n + 1) - f(m) else vec 0`;;

let VSUM_DELETE_CASES = `!x f s.
        FINITE(s:A->bool)
        ==> vsum(s DELETE x) f = if x IN s then vsum s f - f x else vsum s f`;;

let VSUM_EQ_GENERAL = `!s:A->bool t:B->bool (f:A->real^N) g h.
        (!y. y IN t ==> ?!x. x IN s /\ h x = y) /\
        (!x. x IN s ==> h x IN t /\ g(h x) = f x)
        ==> vsum s f = vsum t g`;;

let VSUM_EQ_GENERAL_INVERSES = `!s t (f:A->real^N) (g:B->real^N) h k.
        (!y. y IN t ==> k y IN s /\ h (k y) = y) /\
        (!x. x IN s ==> h x IN t /\ k (h x) = x /\ g (h x) = f x)
        ==> vsum s f = vsum t g`;;

let VSUM_NORM_ALLSUBSETS_BOUND = `!f:A->real^N p e.
        FINITE p /\
        (!q. q SUBSET p ==> norm(vsum q f) <= e)
        ==> sum p (\x. norm(f x)) <= &2 * &(dimindex(:N)) * e`;;

let DOT_LSUM = `!s f y. FINITE s ==> (vsum s f) dot y = sum s (\x. f(x) dot y)`;;

let DOT_RSUM = `!s f x. FINITE s ==> x dot (vsum s f) = sum s (\y. x dot f(y))`;;

let VSUM_OFFSET = `!p f m n. vsum(m + p..n + p) f = vsum(m..n) (\i. f (i + p))`;;

let VSUM_OFFSET_0 = `!f m n. m <= n ==> vsum(m..n) f = vsum(0..n - m) (\i. f (i + m))`;;

let VSUM_TRIV_NUMSEG = `!f m n. n < m ==> vsum(m..n) f = vec 0`;;

let VSUM_CONST_NUMSEG = `!c m n. vsum(m..n) (\n. c) = &((n + 1) - m) % c`;;

let VSUM_SUC = `!f m n. vsum (SUC n..SUC m) f = vsum (n..m) (f o SUC)`;;

let VSUM_BIJECTION = `!f:A->real^N p s:A->bool.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
                ==> vsum s f = vsum s (f o p)`;;

let VSUM_PARTIAL_SUC = `!f g:num->real^N m n.
        vsum (m..n) (\k. f(k) % (g(k + 1) - g(k))) =
            if m <= n then f(n + 1) % g(n + 1) - f(m) % g(m) -
                           vsum (m..n) (\k. (f(k + 1) - f(k)) % g(k + 1))
            else vec 0`;;

let VSUM_PARTIAL_PRE = `!f g:num->real^N m n.
        vsum (m..n) (\k. f(k) % (g(k) - g(k - 1))) =
            if m <= n then f(n + 1) % g(n) - f(m) % g(m - 1) -
                           vsum (m..n) (\k. (f(k + 1) - f(k)) % g(k))
            else vec 0`;;

let VSUM_COMBINE_L = `!f m n p.
        0 < n /\ m <= n /\ n <= p + 1
        ==> vsum(m..n - 1) f + vsum(n..p) f = vsum(m..p) f`;;

let VSUM_COMBINE_R = `!f m n p.
        m <= n + 1 /\ n <= p
        ==> vsum(m..n) f + vsum(n + 1..p) f = vsum(m..p) f`;;

let VSUM_INJECTION = `!f p s.
         FINITE s /\
         (!x. x IN s ==> p x IN s) /\
         (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
         ==> vsum s (f o p) = vsum s f`;;

let VSUM_SWAP = `!f s t.
         FINITE s /\ FINITE t
         ==> vsum s (\i. vsum t (f i)) = vsum t (\j. vsum s (\i. f i j))`;;

let VSUM_SWAP_NUMSEG = `!a b c d f.
         vsum (a..b) (\i. vsum (c..d) (f i)) =
         vsum (c..d) (\j. vsum (a..b) (\i. f i j))`;;

let VSUM_ADD_GEN = `!f g s.
       FINITE {x | x IN s /\ ~(f x = vec 0)} /\
       FINITE {x | x IN s /\ ~(g x = vec 0)}
       ==> vsum s (\x. f x + g x) = vsum s f + vsum s g`;;

let VSUM_CASES_1 = `!s a. FINITE s /\ a IN s
         ==> vsum s (\x. if x = a then y else f(x)) = vsum s f + (y - f a)`;;

let VSUM_SING_NUMSEG = `vsum(n..n) f = f n`;;

let VSUM_1 = `vsum(1..1) f = f(1)`;;

let VSUM_2 = `!t. vsum(1..2) t = t(1) + t(2)`;;

let VSUM_3 = `!t. vsum(1..3) t = t(1) + t(2) + t(3)`;;

let VSUM_4 = `!t. vsum(1..4) t = t(1) + t(2) + t(3) + t(4)`;;

let VSUM_PAIR = `!f:num->real^N m n.
        vsum(2*m..2*n+1) f = vsum(m..n) (\i. f(2*i) + f(2*i+1))`;;

let VSUM_PAIR_0 = `!f:num->real^N n. vsum(0..2*n+1) f = vsum(0..n) (\i. f(2*i) + f(2*i+1))`;;

let VSUM_REFLECT = `!x m n. vsum(m..n) x =
           if n < m then vec 0 else vsum(0..n-m) (\i. x(n - i))`;;

(* ------------------------------------------------------------------------- *)
(* Add useful congruences to the simplifier.                                 *)
(* ------------------------------------------------------------------------- *)

let th = `(!f g s.   (!x. x IN s ==> f(x) = g(x))
              ==> vsum s (\i. f(i)) = vsum s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> vsum(a..b) (\i. f(i)) = vsum(a..b) g) /\
   (!f g p.   (!x. p x ==> f x = g x)
              ==> vsum {y | p y} (\i. f(i)) = vsum {y | p y} g)`;;

(* ------------------------------------------------------------------------- *)
(* A conversion for evaluation of `vsum(m..n) f` for numerals m and n.       *)
(* ------------------------------------------------------------------------- *)

let EXPAND_VSUM_CONV =
  let [pth_0; pth_1; pth_2] = (CONJUNCTS o prove)
   (`(n < m ==> vsum(m..n) (f:num->real^N) = vec 0) /\
     vsum(m..m) (f:num->real^N) = f m /\
     (m <= n ==> vsum (m..n) (f:num->real^N) = f m + vsum (m + 1..n) f)`,
    REWRITE_TAC[VSUM_CLAUSES_LEFT; VSUM_SING_NUMSEG; VSUM_TRIV_NUMSEG])
  and ns_tm = `..` and f_tm = `f:num->real^N`
  and m_tm = `m:num` and n_tm = `n:num`
  and n_ty = `:N` in
  let rec conv tm =
    let smn,ftm = dest_comb tm in
    let s,mn = dest_comb smn in
    if not(is_const s && fst(dest_const s) = "vsum")
    then failwith "EXPAND_VSUM_CONV" else
    let mtm,ntm = dest_binop ns_tm mn in
    let m = dest_numeral mtm and n = dest_numeral ntm in
    let nty = hd(tl(snd(dest_type(snd(dest_fun_ty(type_of ftm)))))) in
    let ilist = [nty,n_ty] in
    let ifn = inst ilist and tfn = INST_TYPE ilist in
    if n < m then
      let th1 = INST [ftm,ifn f_tm; mtm,m_tm; ntm,n_tm] (tfn pth_0) in
      MP th1 (EQT_ELIM(NUM_LT_CONV(lhand(concl th1))))
    else if n = m then CONV_RULE (RAND_CONV(TRY_CONV BETA_CONV))
                                 (INST [ftm,ifn f_tm; mtm,m_tm] (tfn pth_1))
    else
      let th1 = INST [ftm,ifn f_tm; mtm,m_tm; ntm,n_tm] (tfn pth_2) in
      let th2 = MP th1 (EQT_ELIM(NUM_LE_CONV(lhand(concl th1)))) in
      CONV_RULE (RAND_CONV(COMB2_CONV (RAND_CONV(TRY_CONV BETA_CONV))
       (LAND_CONV(LAND_CONV NUM_ADD_CONV) THENC conv))) th2 in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Basis vectors in coordinate directions.                                   *)
(* ------------------------------------------------------------------------- *)

let basis = new_definition
  `basis k = lambda i. if i = k then &1 else &0`;;

let NORM_BASIS = `!k. 1 <= k /\ k <= dimindex(:N)
       ==> (norm(basis k :real^N) = &1)`;;

let NORM_BASIS_1 = `norm(basis 1) = &1`;;

let VECTOR_CHOOSE_SIZE = `!c. &0 <= c ==> ?x:real^N. norm(x) = c`;;

let VECTOR_CHOOSE_DIST = `!x e. &0 <= e ==> ?y:real^N. dist(x,y) = e`;;

let BASIS_INJ = `!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N) /\
         (basis i :real^N = basis j)
         ==> (i = j)`;;

let BASIS_INJ_EQ = `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
         ==> (basis i:real^N = basis j <=> i = j)`;;

let BASIS_NE = `!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N) /\
         ~(i = j)
         ==> ~(basis i :real^N = basis j)`;;

let BASIS_COMPONENT = `!k i. 1 <= i /\ i <= dimindex(:N)
         ==> ((basis k :real^N)$i = if i = k then &1 else &0)`;;

let BASIS_EXPANSION = `!x:real^N. vsum(1..dimindex(:N)) (\i. x$i % basis i) = x`;;

let BASIS_EXPANSION_UNIQUE = `!f x:real^N. (vsum(1..dimindex(:N)) (\i. f(i) % basis i) = x) <=>
                (!i. 1 <= i /\ i <= dimindex(:N) ==> f(i) = x$i)`;;

let DOT_BASIS = `!x:real^N i.
        1 <= i /\ i <= dimindex(:N)
        ==> ((basis i) dot x = x$i) /\ (x dot (basis i) = x$i)`;;

let DOT_BASIS_BASIS = `!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N)
         ==> (basis i:real^N) dot (basis j) = if i = j then &1 else &0`;;

let DOT_BASIS_BASIS_UNEQUAL = `!i j. ~(i = j) ==> (basis i) dot (basis j) = &0`;;

let BASIS_EQ_0 = `!i. (basis i :real^N = vec 0) <=> ~(i IN 1..dimindex(:N))`;;

let BASIS_NONZERO = `!k. 1 <= k /\ k <= dimindex(:N)
       ==> ~(basis k :real^N = vec 0)`;;

let VECTOR_EQ_LDOT = `!y z. (!x. x dot y = x dot z) <=> y = z`;;

let VECTOR_EQ_RDOT = `!x y. (!z. x dot z = y dot z) <=> x = y`;;

(* ------------------------------------------------------------------------- *)
(* Orthogonality.                                                            *)
(* ------------------------------------------------------------------------- *)

let orthogonal = new_definition
  `orthogonal x y <=> (x dot y = &0)`;;

let ORTHOGONAL_0 = `!x. orthogonal (vec 0) x /\ orthogonal x (vec 0)`;;

let ORTHOGONAL_REFL = `!x. orthogonal x x <=> x = vec 0`;;

let ORTHOGONAL_SYM = `!x y. orthogonal x y <=> orthogonal y x`;;

let ORTHOGONAL_LNEG = `!x y. orthogonal (--x) y <=> orthogonal x y`;;

let ORTHOGONAL_RNEG = `!x y. orthogonal x (--y) <=> orthogonal x y`;;

let ORTHOGONAL_MUL = `(!a x y:real^N. orthogonal (a % x) y <=> a = &0 \/ orthogonal x y) /\
   (!a x y:real^N. orthogonal x (a % y) <=> a = &0 \/ orthogonal x y)`;;

let ORTHOGONAL_BASIS = `!x:real^N i. 1 <= i /\ i <= dimindex(:N)
                ==> (orthogonal (basis i) x <=> (x$i = &0))`;;

let ORTHOGONAL_BASIS_BASIS = `!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N)
         ==> (orthogonal (basis i :real^N) (basis j) <=> ~(i = j))`;;

let ORTHOGONAL_CLAUSES = `(!a. orthogonal a (vec 0)) /\
   (!a x c. orthogonal a x ==> orthogonal a (c % x)) /\
   (!a x. orthogonal a x ==> orthogonal a (--x)) /\
   (!a x y. orthogonal a x /\ orthogonal a y ==> orthogonal a (x + y)) /\
   (!a x y. orthogonal a x /\ orthogonal a y ==> orthogonal a (x - y)) /\
   (!a. orthogonal (vec 0) a) /\
   (!a x c. orthogonal x a ==> orthogonal (c % x) a) /\
   (!a x. orthogonal x a ==> orthogonal (--x) a) /\
   (!a x y. orthogonal x a /\ orthogonal y a ==> orthogonal (x + y) a) /\
   (!a x y. orthogonal x a /\ orthogonal y a ==> orthogonal (x - y) a)`;;

let ORTHOGONAL_RVSUM = `!f:A->real^N s x.
        FINITE s /\
        (!y. y IN s ==> orthogonal x (f y))
        ==> orthogonal x (vsum s f)`;;

let ORTHOGONAL_LVSUM = `!f:A->real^N s y.
        FINITE s /\
        (!x. x IN s ==> orthogonal (f x) y)
        ==> orthogonal (vsum s f) y`;;

let NORM_ADD_PYTHAGOREAN = `!a b:real^N.
        orthogonal a b
        ==> norm(a + b) pow 2 = norm(a) pow 2 + norm(b) pow 2`;;

let NORM_VSUM_PYTHAGOREAN = `!k u:A->real^N.
        FINITE k /\ pairwise (\i j. orthogonal (u i) (u j)) k
        ==> norm(vsum k u) pow 2 = sum k (\i. norm(u i) pow 2)`;;

(* ------------------------------------------------------------------------- *)
(* Explicit vector construction from lists.                                  *)
(* ------------------------------------------------------------------------- *)

let VECTOR_1 = `(vector[x]:A^1)$1 = x`;;

let VECTOR_2 = `(vector[x;y]:A^2)$1 = x /\
   (vector[x;y]:A^2)$2 = y`;;

let VECTOR_3 = `(vector[x;y;z]:A^3)$1 = x /\
   (vector[x;y;z]:A^3)$2 = y /\
   (vector[x;y;z]:A^3)$3 = z`;;

let VECTOR_4 = `(vector[w;x;y;z]:A^4)$1 = w /\
   (vector[w;x;y;z]:A^4)$2 = x /\
   (vector[w;x;y;z]:A^4)$3 = y /\
   (vector[w;x;y;z]:A^4)$4 = z`;;

let FORALL_VECTOR_1 = `(!v:A^1. P v) <=> !x. P(vector[x])`;;

let FORALL_VECTOR_2 = `(!v:A^2. P v) <=> !x y. P(vector[x;y])`;;

let FORALL_VECTOR_3 = `(!v:A^3. P v) <=> !x y z. P(vector[x;y;z])`;;

let FORALL_VECTOR_4 = `(!v:A^4. P v) <=> !w x y z. P(vector[w;x;y;z])`;;

let EXISTS_VECTOR_1 = `(?v:A^1. P v) <=> ?x. P(vector[x])`;;

let EXISTS_VECTOR_2 = `(?v:A^2. P v) <=> ?x y. P(vector[x;y])`;;

let EXISTS_VECTOR_3 = `(?v:A^3. P v) <=> ?x y z. P(vector[x;y;z])`;;

let EXISTS_VECTOR_4 = `(?v:A^4. P v) <=> ?w x y z. P(vector[w;x;y;z])`;;

let VECTOR_EXPAND_1 = `!x:real^1. x = vector[x$1]`;;

let VECTOR_EXPAND_2 = `!x:real^2. x = vector[x$1;x$2]`;;

let VECTOR_EXPAND_3 = `!x:real^3. x = vector[x$1;x$2;x$3]`;;

let VECTOR_EXPAND_4 = `!x:real^4. x = vector[x$1;x$2;x$3;x$4]`;;

(* ------------------------------------------------------------------------- *)
(* Linear functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let linear = new_definition
  `linear (f:real^M->real^N) <=>
        (!x y. f(x + y) = f(x) + f(y)) /\
        (!c x. f(c % x) = c % f(x))`;;

let LINEAR_COMPOSE_CMUL = `!f c. linear f ==> linear (\x. c % f(x))`;;

let LINEAR_COMPOSE_NEG = `!f. linear f ==> linear (\x. --(f(x)))`;;

let LINEAR_COMPOSE_NEG_EQ = `!f:real^M->real^N. linear(\x. --(f x)) <=> linear f`;;

let LINEAR_COMPOSE_ADD = `!f g. linear f /\ linear g ==> linear (\x. f(x) + g(x))`;;

let LINEAR_COMPOSE_SUB = `!f g. linear f /\ linear g ==> linear (\x. f(x) - g(x))`;;

let LINEAR_COMPOSE = `!f g. linear f /\ linear g ==> linear (g o f)`;;

let LINEAR_ID = `linear (\x. x)`;;

let LINEAR_I = `linear I`;;

let LINEAR_ZERO = `linear (\x. vec 0)`;;

let LINEAR_NEGATION = `linear(--)`;;

let LINEAR_COMPOSE_VSUM = `!f s. FINITE s /\ (!a. a IN s ==> linear(f a))
         ==> linear(\x. vsum s (\a. f a x))`;;

let LINEAR_VMUL_COMPONENT = `!f:real^M->real^N v k.
     linear f /\ 1 <= k /\ k <= dimindex(:N)
     ==> linear (\x. f(x)$k % v)`;;

let LINEAR_0 = `!f. linear f ==> (f(vec 0) = vec 0)`;;

let LINEAR_CMUL = `!f c x. linear f ==> (f(c % x) = c % f(x))`;;

let LINEAR_NEG = `!f x. linear f ==> (f(--x) = --(f x))`;;

let LINEAR_ADD = `!f x y. linear f ==> (f(x + y) = f(x) + f(y))`;;

let LINEAR_SUB = `!f x y. linear f ==> (f(x - y) = f(x) - f(y))`;;

let LINEAR_VSUM = `!f g s. linear f /\ FINITE s ==> (f(vsum s g) = vsum s (f o g))`;;

let LINEAR_VSUM_MUL = `!f s c v.
        linear f /\ FINITE s
        ==> f(vsum s (\i. c i % v i)) = vsum s (\i. c(i) % f(v i))`;;

let LINEAR_INJECTIVE_0 = `!f. linear f
       ==> ((!x y. (f(x) = f(y)) ==> (x = y)) <=>
            (!x. (f(x) = vec 0) ==> (x = vec 0)))`;;

let LINEAR_BOUNDED = `!f:real^M->real^N. linear f ==> ?B. !x. norm(f x) <= B * norm(x)`;;

let LINEAR_BOUNDED_POS = `!f:real^M->real^N. linear f ==> ?B. &0 < B /\ !x. norm(f x) <= B * norm(x)`;;

let SYMMETRIC_LINEAR_IMAGE = `!f s. (!x. x IN s ==> --x IN s) /\ linear f
          ==> !x. x IN (IMAGE f s) ==> --x IN (IMAGE f s)`;;

(* ------------------------------------------------------------------------- *)
(* Bilinear functions.                                                       *)
(* ------------------------------------------------------------------------- *)

let bilinear = new_definition
  `bilinear f <=> (!x. linear(\y. f x y)) /\ (!y. linear(\x. f x y))`;;

let BILINEAR_SWAP = `!op:real^M->real^N->real^P.
        bilinear(\x y. op y x) <=> bilinear op`;;

let BILINEAR_LADD = `!h x y z. bilinear h ==> h (x + y) z = (h x z) + (h y z)`;;

let BILINEAR_RADD = `!h x y z. bilinear h ==> h x (y + z) = (h x y) + (h x z)`;;

let BILINEAR_LMUL = `!h c x y. bilinear h ==> h (c % x) y = c % (h x y)`;;

let BILINEAR_RMUL = `!h c x y. bilinear h ==> h x (c % y) = c % (h x y)`;;

let BILINEAR_LNEG = `!h x y. bilinear h ==> h (--x) y = --(h x y)`;;

let BILINEAR_RNEG = `!h x y. bilinear h ==> h x (--y) = --(h x y)`;;

let BILINEAR_LZERO = `!h x. bilinear h ==> h (vec 0) x = vec 0`;;

let BILINEAR_RZERO = `!h x. bilinear h ==> h x (vec 0) = vec 0`;;

let BILINEAR_LSUB = `!h x y z. bilinear h ==> h (x - y) z = (h x z) - (h y z)`;;

let BILINEAR_RSUB = `!h x y z. bilinear h ==> h x (y - z) = (h x y) - (h x z)`;;

let BILINEAR_LSUM = `!bop:real^M->real^N->real^P f s:A->bool y.
        bilinear bop /\ FINITE s
        ==> bop(vsum s f) y = vsum s (\i. bop (f i) y)`;;

let BILINEAR_RSUM = `!bop:real^M->real^N->real^P f s:A->bool x.
        bilinear bop /\ FINITE s
        ==> bop x (vsum s f) = vsum s (\i. bop x (f i))`;;

let BILINEAR_VSUM = `!h:real^M->real^N->real^P.
       bilinear h /\ FINITE s /\ FINITE t
       ==> h (vsum s f) (vsum t g) = vsum (s CROSS t) (\(i,j). h (f i) (g j))`;;

let BILINEAR_BOUNDED = `!h:real^M->real^N->real^P.
        bilinear h ==> ?B. !x y. norm(h x y) <= B * norm(x) * norm(y)`;;

let BILINEAR_BOUNDED_POS = `!h. bilinear h
       ==> ?B. &0 < B /\ !x y. norm(h x y) <= B * norm(x) * norm(y)`;;

let BILINEAR_VSUM_PARTIAL_SUC = `!f g h:real^M->real^N->real^P m n.
        bilinear h
        ==> vsum (m..n) (\k. h (f k) (g(k + 1) - g(k))) =
                if m <= n then h (f(n + 1)) (g(n + 1)) - h (f m) (g m) -
                               vsum (m..n) (\k. h (f(k + 1) - f(k)) (g(k + 1)))
                else vec 0`;;

let BILINEAR_VSUM_PARTIAL_PRE = `!f g h:real^M->real^N->real^P m n.
        bilinear h
        ==> vsum (m..n) (\k. h (f k) (g(k) - g(k - 1))) =
                if m <= n then h (f(n + 1)) (g(n)) - h (f m) (g(m - 1)) -
                               vsum (m..n) (\k. h (f(k + 1) - f(k)) (g(k)))
                else vec 0`;;

let BILINEAR_VSUM_CONVOLUTION_1 = `!bop:real^M->real^N->real^P a b n.
        bilinear bop
        ==> vsum(0..n) (\m. vsum (0..m) (\i. bop (a i) (b(m - i)))) =
            vsum(0..n) (\m. bop (a m) (vsum(0..n-m) b))`;;

let BILINEAR_VSUM_CONVOLUTION_2 = `!bop:real^M->real^N->real^P a b n.
    bilinear bop
    ==> vsum(0..n) (\m. vsum(0..m) (\k. vsum(0..k) (\i. bop (a i) (b(k-i))))) =
        vsum(0..n) (\m. bop (vsum(0..m) a) (vsum(0..n-m) b))`;;

(* ------------------------------------------------------------------------- *)
(* Adjoints.                                                                 *)
(* ------------------------------------------------------------------------- *)

let adjoint = new_definition
 `adjoint(f:real^M->real^N) = @f'. !x y. f(x) dot y = x dot f'(y)`;;

let ADJOINT_WORKS = `!f:real^M->real^N. linear f ==> !x y. f(x) dot y = x dot (adjoint f)(y)`;;

let ADJOINT_LINEAR = `!f:real^M->real^N. linear f ==> linear(adjoint f)`;;

let ADJOINT_CLAUSES = `!f:real^M->real^N.
     linear f ==> (!x y. x dot (adjoint f)(y) = f(x) dot y) /\
                  (!x y. (adjoint f)(y) dot x = y dot f(x))`;;

let ADJOINT_ADJOINT = `!f:real^M->real^N. linear f ==> adjoint(adjoint f) = f`;;

let ADJOINT_UNIQUE = `!f f'. linear f /\ (!x y. f'(x) dot y = x dot f(y))
          ==> f' = adjoint f`;;

let ADJOINT_COMPOSE = `!f g:real^N->real^N.
        linear f /\ linear g ==> adjoint(f o g) = adjoint g o adjoint f`;;

let SELF_ADJOINT_COMPOSE = `!f g:real^N->real^N.
        linear f /\ linear g /\ adjoint f = f /\ adjoint g = g
        ==> (adjoint(f o g) = f o g <=> f o g = g o f)`;;

let SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS = `!f:real^N->real^N v w a b.
        linear f /\ adjoint f = f /\ f v = a % v /\ f w = b % w /\ ~(a = b)
        ==> orthogonal v w`;;

let ORTHOGONAL_PROJECTION_ALT = `!f:real^N->real^N.
        linear f
        ==> ((!x y. orthogonal (f x - x) (f x - f y)) <=>
             (!x y. orthogonal (f x - x) (f y)))`;;

let ORTHOGONAL_PROJECTION_EQ_SELF_ADJOINT_IDEMPOTENT = `!f:real^N->real^N.
        linear f
        ==> ((!x y. orthogonal (f x - x) (f x - f y)) <=>
             adjoint f = f /\ f o f = f)`;;

(* ------------------------------------------------------------------------- *)
(* Some basics about Lipschitz functions.                                    *)
(* ------------------------------------------------------------------------- *)

let LIPSCHITZ_ON_POS = `!f:real^M->real^N s.
        (?B. !x y. x IN s /\ y IN s
                   ==> norm(f x - f y) <= B * norm(x - y)) <=>
        (?B. &0 < B /\
             !x y. x IN s /\ y IN s
                   ==> norm(f x - f y) <= B * norm(x - y))`;;

let LIPSCHITZ_POS = `!f:real^M->real^N.
        (?B. !x y. norm(f x - f y) <= B * norm(x - y)) <=>
        (?B. &0 < B /\ !x y. norm(f x - f y) <= B * norm(x - y))`;;

let LIPSCHITZ_ON_COMPOSE = `!f:real^M->real^N g:real^N->real^P s t.
        (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y)) /\
        (?B. !x y. x IN t /\ y IN t ==> norm(g x - g y) <= B * norm(x - y)) /\
        IMAGE f s SUBSET t
        ==> ?B. !x y. x IN s /\ y IN s
                      ==> norm(g(f x) - g(f y)) <= B * norm(x - y)`;;

let LINEAR_IMP_LIPSCHITZ = `!f:real^M->real^N.
        linear f ==> ?B. !x y. norm(f x - f y) <= B * norm(x - y)`;;

let LIPSCHITZ_ON_COMPONENTWISE = `!f:real^M->real^N s.
      (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y)) <=>
      !i. 1 <= i /\ i <= dimindex(:N)
          ==> ?B. !x y. x IN s /\ y IN s
                        ==> abs(f x$i - f y$i) <= B * norm(x - y)`;;

(* ------------------------------------------------------------------------- *)
(* Matrix notation. NB: an MxN matrix is of type real^N^M, not real^M^N.     *)
(* We could define a special type if we're going to use them a lot.          *)
(* ------------------------------------------------------------------------- *)

overload_interface ("--",`(matrix_neg):real^N^M->real^N^M`);;
overload_interface ("+",`(matrix_add):real^N^M->real^N^M->real^N^M`);;
overload_interface ("-",`(matrix_sub):real^N^M->real^N^M->real^N^M`);;

make_overloadable "**" `:A->B->C`;;

overload_interface ("**",`(vector_matrix_mul):real^M->real^N^M->real^N`);;
overload_interface ("**",`(matrix_mul):real^N^M->real^P^N->real^P^M`);;
overload_interface ("**",`(matrix_vector_mul):real^N^M->real^N->real^M`);;

parse_as_infix("%%",(21,"right"));;

prioritize_real();;

let matrix_cmul = new_definition
  `((%%):real->real^N^M->real^N^M) c A = lambda i j. c * A$i$j`;;

let matrix_neg = new_definition
  `!A:real^N^M. --A = lambda i j. --(A$i$j)`;;

let matrix_add = new_definition
  `!A:real^N^M B:real^N^M. A + B = lambda i j. A$i$j + B$i$j`;;

let matrix_sub = new_definition
  `!A:real^N^M B:real^N^M. A - B = lambda i j. A$i$j - B$i$j`;;

let matrix_mul = new_definition
  `!A:real^N^M B:real^P^N.
        A ** B =
          lambda i j. sum(1..dimindex(:N)) (\k. A$i$k * B$k$j)`;;

let matrix_vector_mul = new_definition
  `!A:real^N^M x:real^N.
        A ** x = lambda i. sum(1..dimindex(:N)) (\j. A$i$j * x$j)`;;

let vector_matrix_mul = new_definition
  `!A:real^N^M x:real^M.
        x ** A = lambda j. sum(1..dimindex(:M)) (\i. A$i$j * x$i)`;;

let mat = new_definition
  `(mat:num->real^N^M) k = lambda i j. if i = j then &k else &0`;;

let transp = new_definition
  `(transp:real^N^M->real^M^N) A = lambda i j. A$j$i`;;

let row = new_definition
 `(row:num->real^N^M->real^N) i A = lambda j. A$i$j`;;

let column = new_definition
 `(column:num->real^N^M->real^M) j A = lambda i. A$i$j`;;

let rows = new_definition
 `rows(A:real^N^M) = { row i A | 1 <= i /\ i <= dimindex(:M)}`;;

let columns = new_definition
 `columns(A:real^N^M) = { column i A | 1 <= i /\ i <= dimindex(:N)}`;;

let MATRIX_CMUL_COMPONENT = `!c A:real^N^M i. (c %% A)$i$j = c * A$i$j`;;

let MATRIX_ADD_COMPONENT = `!A B:real^N^M i j. (A + B)$i$j = A$i$j + B$i$j`;;

let MATRIX_SUB_COMPONENT = `!A B:real^N^M i j. (A - B)$i$j = A$i$j - B$i$j`;;

let MATRIX_NEG_COMPONENT = `!A:real^N^M i j. (--A)$i$j = --(A$i$j)`;;

let TRANSP_COMPONENT = `!A:real^N^M i j. (transp A)$i$j = A$j$i`;;

let MAT_COMPONENT = `!n i j.
        1 <= i /\ i <= dimindex(:M) /\
        1 <= j /\ j <= dimindex(:N)
        ==> (mat n:real^N^M)$i$j = if i = j then &n else &0`;;

let MAT_0_COMPONENT = `!i j. (mat 0:real^N^M)$i$j = &0`;;

let MATRIX_ADD_ROW = `!X Y:real^M^N i. (X + Y)$i = X$i + Y$i`;;

let MATRIX_SUB_ROW = `!X Y:real^M^N i. (X - Y)$i = X$i - Y$i`;;

let MATRIX_NEG_ROW = `!X:real^M^N i. (--X)$i = --(X$i)`;;

let MATRIX_CMUL_ROW = `!c X:real^M^N i. (c %% X)$i = c % X$i`;;

let MAT_0_ROW = `mat 0:real^M^N$i = vec 0`;;

(* ------------------------------------------------------------------------- *)
(* Symmetric and normal matrices                                             *)
(* ------------------------------------------------------------------------- *)

let symmetric_matrix = new_definition
 `symmetric_matrix (A:real^N^N) <=> transp A = A`;;

let normal_matrix = new_definition
 `normal_matrix (A:real^N^N) <=> transp A ** A = A ** transp A`;;

let SYMMETRIC_IMP_NORMAL_MATRIX = `!A:real^N^N. symmetric_matrix A ==> normal_matrix A`;;

(* ------------------------------------------------------------------------- *)
(* A decision procedure for matrices analogous to VECTOR_ARITH.              *)
(* ------------------------------------------------------------------------- *)

let MATRIX_ARITH_TAC =
  let CART2_EQ_FULL = `!x y:A^M^N. x = y <=> (!i j. x$i$j = y$i$j)`;;

let MAT_CMUL = `!a. mat a = &a %% mat 1`;;

let ROW_0 = `!i. row i (mat 0:real^N^N) = vec 0`;;

let COLUMN_0 = `!i. column i (mat 0:real^N^N) = vec 0`;;

let MATRIX_CMUL_ASSOC = `!a b X:real^M^N. a %% (b %% X) = (a * b) %% X`;;

let MATRIX_CMUL_LID = `!X:real^M^N. &1 %% X = X`;;

let MATRIX_ADD_SYM = `!A:real^N^M B. A + B = B + A`;;

let MATRIX_ADD_ASSOC = `!A:real^N^M B C. A + (B + C) = (A + B) + C`;;

let MATRIX_ADD_LID = `!A. mat 0 + A = A`;;

let MATRIX_ADD_RID = `!A. A + mat 0 = A`;;

let MATRIX_ADD_LNEG = `!A. --A + A = mat 0`;;

let MATRIX_ADD_RNEG = `!A. A + --A = mat 0`;;

let MATRIX_SUB = `!A:real^N^M B. A - B = A + --B`;;

let MATRIX_SUB_REFL = `!A. A - A = mat 0`;;

let MATRIX_SUB_EQ = `!A B:real^N^M. A - B = mat 0 <=> A = B`;;

let MATRIX_SUB_ADD = `!A B:real^N^M. (A - B) + B = A`;;

let MATRIX_SUB_ADD2 = `!A B:real^N^M. A + (B - A) = B`;;

let MATRIX_ADD_LDISTRIB = `!A:real^N^M B:real^P^N C. A ** (B + C) = A ** B + A ** C`;;

let MATRIX_MUL_LID = `!A:real^N^M. mat 1 ** A = A`;;

let MATRIX_MUL_RID = `!A:real^N^M. A ** mat 1 = A`;;

let MATRIX_MUL_ASSOC = `!A:real^N^M B:real^P^N C:real^Q^P. A ** B ** C = (A ** B) ** C`;;

let MATRIX_MUL_LZERO = `!A. (mat 0:real^N^M) ** (A:real^P^N) = mat 0`;;

let MATRIX_MUL_RZERO = `!A. (A:real^N^M) ** (mat 0:real^P^N) = mat 0`;;

let MATRIX_ADD_RDISTRIB = `!A:real^N^M B C:real^P^N. (A + B) ** C = A ** C + B ** C`;;

let MATRIX_SUB_LDISTRIB = `!A:real^N^M B C:real^P^N. A ** (B - C) = A ** B - A ** C`;;

let MATRIX_SUB_RDISTRIB = `!A:real^N^M B C:real^P^N. (A - B) ** C = A ** C - B ** C`;;

let MATRIX_MUL_LMUL = `!A:real^N^M B:real^P^N c. (c %% A) ** B = c %% (A ** B)`;;

let MATRIX_MUL_RMUL = `!A:real^N^M B:real^P^N c. A ** (c %% B) = c %% (A ** B)`;;

let MATRIX_CMUL_ADD_LDISTRIB = `!A:real^N^M B c. c %% (A + B) = c %% A + c %% B`;;

let MATRIX_CMUL_SUB_LDISTRIB = `!A:real^N^M B c. c %% (A - B) = c %% A - c %% B`;;

let MATRIX_CMUL_ADD_RDISTRIB = `!A:real^N^M b c. (b + c) %% A = b %% A + c %% A`;;

let MATRIX_CMUL_SUB_RDISTRIB = `!A:real^N^M b c. (b - c) %% A = b %% A - c %% A`;;

let MATRIX_CMUL_RZERO = `!c. c %% mat 0 = mat 0`;;

let MATRIX_CMUL_LZERO = `!A. &0 %% A = mat 0`;;

let MATRIX_NEG_MINUS1 = `!A:real^N^M. --A = --(&1) %% A`;;

let MATRIX_ADD_AC = `(A:real^N^M) + B = B + A /\
   (A + B) + C = A + (B + C) /\
   A + (B + C) = B + (A + C)`;;

let MATRIX_NEG_ADD = `!A B:real^N^M. --(A + B) = --A + --B`;;

let MATRIX_NEG_SUB = `!A B:real^N^M. --(A - B) = B - A`;;

let MATRIX_NEG_0 = `--(mat 0) = mat 0`;;

let MATRIX_SUB_RZERO = `!A:real^N^M. A - mat 0 = A`;;

let MATRIX_SUB_LZERO = `!A:real^N^M. mat 0 - A = --A`;;

let MATRIX_NEG_EQ_0 = `!A:real^N^M. --A = mat 0 <=> A = mat 0`;;

let MATRIX_VECTOR_MUL_ASSOC = `!A:real^N^M B:real^P^N x:real^P. A ** B ** x = (A ** B) ** x`;;

let MATRIX_VECTOR_MUL_LID = `!x:real^N. mat 1 ** x = x`;;

let MATRIX_VECTOR_MUL_LZERO = `!x:real^N. mat 0 ** x = vec 0`;;

let MATRIX_VECTOR_MUL_RZERO = `!A:real^M^N. A ** vec 0 = vec 0`;;

let MATRIX_VECTOR_MUL_ADD_LDISTRIB = `!A:real^M^N x:real^M y. A ** (x + y) = A ** x + A ** y`;;

let MATRIX_VECTOR_MUL_SUB_LDISTRIB = `!A:real^M^N x:real^M y. A ** (x - y) = A ** x - A ** y`;;

let MATRIX_VECTOR_MUL_ADD_RDISTRIB = `!A:real^M^N B x:real^M. (A + B) ** x = (A ** x) + (B ** x)`;;

let MATRIX_VECTOR_MUL_SUB_RDISTRIB = `!A:real^M^N B x:real^M. (A - B) ** x = (A ** x) - (B ** x)`;;

let MATRIX_VECTOR_MUL_RMUL = `!A:real^M^N x:real^M c. A ** (c % x) = c % (A ** x)`;;

let MATRIX_MUL_LNEG = `!A:real^N^M B:real^P^N. (--A) ** B = --(A ** B)`;;

let MATRIX_MUL_RNEG = `!A:real^N^M B:real^P^N. A ** --B = --(A ** B)`;;

let MATRIX_NEG_NEG = `!A:real^N^M. --(--A) = A`;;

let MATRIX_TRANSP_MUL = `!A B. transp(A ** B) = transp(B) ** transp(A)`;;

let TRANSP_EQ_0 = `!A:real^N^M. transp A = mat 0 <=> A = mat 0`;;

let SYMMETRIC_MATRIX_MUL = `!A B:real^N^N.
        symmetric_matrix A /\ symmetric_matrix B
        ==> (symmetric_matrix(A ** B) <=> A ** B = B ** A)`;;

let MATRIX_EQ = `!A:real^N^M B. (A = B) = !x:real^N. A ** x = B ** x`;;

let MATRIX_EQ_0 = `!A:real^N^N. A = mat 0 <=> !x. A ** x = vec 0`;;

let MATRIX_VECTOR_MUL_COMPONENT = `!A:real^N^M x k.
    1 <= k /\ k <= dimindex(:M) ==> ((A ** x)$k = (A$k) dot x)`;;

let DOT_LMUL_MATRIX = `!A:real^N^M x:real^M y:real^N. (x ** A) dot y = x dot (A ** y)`;;

let TRANSP_MATRIX_CMUL = `!A:real^M^N c. transp(c %% A) = c %% transp A`;;

let SYMMETRIC_MATRIX_CMUL = `!c A:real^N^N.
        symmetric_matrix A ==> symmetric_matrix(c %% A)`;;

let TRANSP_MATRIX_ADD = `!A B:real^N^M. transp(A + B) = transp A + transp B`;;

let SYMMETRIC_MATRIX_ADD = `!A B:real^N^N.
        symmetric_matrix A /\ symmetric_matrix B
        ==> symmetric_matrix(A + B)`;;

let TRANSP_MATRIX_SUB = `!A B:real^N^M. transp(A - B) = transp A - transp B`;;

let SYMMETRIC_MATRIX_SUB = `!A B:real^N^N.
        symmetric_matrix A /\ symmetric_matrix B
        ==> symmetric_matrix(A - B)`;;

let TRANSP_MATRIX_NEG = `!A:real^N^M. transp(--A) = --(transp A)`;;

let SYMMETRIC_MATRIX_NEG = `!A:real^N^N. symmetric_matrix(--A) <=> symmetric_matrix A`;;

let TRANSP_MAT = `!n. transp(mat n) = mat n`;;

let TRANSP_TRANSP = `!A:real^N^M. transp(transp A) = A`;;

let SYMMETRIC_MATRIX_MAT = `!n. symmetric_matrix(mat n)`;;

let SYMMETRIC_MATRIX_COVARIANCE = `!A:real^N^M. symmetric_matrix(transp A ** A)`;;

let SYMMETRIC_MATRIX_SIMILAR = `!A B:real^N^N.
        symmetric_matrix B ==> symmetric_matrix(transp A ** B ** A)`;;

let TRANSP_EQ = `!A B:real^M^N. transp A = transp B <=> A = B`;;

let ROW_TRANSP = `!A:real^N^M i.
        1 <= i /\ i <= dimindex(:N) ==> row i (transp A) = column i A`;;

let COLUMN_TRANSP = `!A:real^N^M i.
        1 <= i /\ i <= dimindex(:M) ==> column i (transp A) = row i A`;;

let ROWS_TRANSP = `!A:real^N^M. rows(transp A) = columns A`;;

let COLUMNS_TRANSP = `!A:real^N^M. columns(transp A) = rows A`;;

let VECTOR_MATRIX_MUL_TRANSP = `!A:real^M^N x:real^N. x ** A = transp A ** x`;;

let MATRIX_VECTOR_MUL_TRANSP = `!A:real^M^N x:real^M. A ** x = x ** transp A`;;

let ROWS_NONEMPTY = `!A:real^N^M. ~(rows A = {})`;;

let COLUMNS_NONEMPTY = `!A:real^N^M. ~(columns A = {})`;;

let FINITE_ROWS = `!A:real^N^M. FINITE(rows A)`;;

let FINITE_COLUMNS = `!A:real^N^M. FINITE(columns A)`;;

let CARD_ROWS_LE = `!A:real^M^N. CARD(rows A) <= dimindex(:N)`;;

let CARD_COLUMNS_LE = `!A:real^M^N. CARD(columns A) <= dimindex(:M)`;;

let MATRIX_EQUAL_ROWS = `!A B:real^N^M.
        A = B <=> !i. 1 <= i /\ i <= dimindex(:M) ==> row i A = row i B`;;

let MATRIX_EQUAL_COLUMNS = `!A B:real^N^M.
        A = B <=> !i. 1 <= i /\ i <= dimindex(:N) ==> column i A = column i B`;;

let MATRIX_CMUL_EQ_0 = `!A:real^M^N c. c %% A = mat 0 <=> c = &0 \/ A = mat 0`;;

let MAT_EQ = `!m n. mat m = mat n <=> m = n`;;

let MATRIX_VECTOR_LMUL = `!A:real^M^N c x:real^M. (c %% A) ** x = c % (A ** x)`;;

let MATRIX_VECTOR_MUL_LNEG = `!A:real^M^N x:real^M. --A ** x = --(A ** x)`;;

let MATRIX_VECTOR_MUL_RNEG = `!A:real^M^N x:real^M. A ** --x = --(A ** x)`;;

let COLUMN_MATRIX_MUL = `!A:real^N^M B:real^P^N.
      1 <= i /\ i <= dimindex(:P) ==> column i (A ** B) = A ** column i B`;;

let ROW_MATRIX_MUL = `!A:real^N^M B:real^P^N.
      1 <= i /\ i <= dimindex(:M) ==> row i (A ** B) = transp B ** row i A`;;

(* ------------------------------------------------------------------------- *)
(* Two sometimes fruitful ways of looking at matrix-vector multiplication.   *)
(* ------------------------------------------------------------------------- *)

let MATRIX_MUL_DOT = `!A:real^N^M x. A ** x = lambda i. A$i dot x`;;

let MATRIX_MUL_VSUM = `!A:real^N^M x. A ** x = vsum(1..dimindex(:N)) (\i. x$i % column i A)`;;

(* ------------------------------------------------------------------------- *)
(* Slightly gruesome lemmas: better to define sums over vectors really...    *)
(* ------------------------------------------------------------------------- *)

let VECTOR_COMPONENTWISE = `!x:real^N.
    x = lambda j. sum(1..dimindex(:N))
                     (\i. x$i * (basis i :real^N)$j)`;;

let LINEAR_COMPONENTWISE_EXPANSION = `!f:real^M->real^N.
      linear(f)
      ==> !x j. 1 <= j /\ j <= dimindex(:N)
                ==> (f x $j =
                     sum(1..dimindex(:M)) (\i. x$i * f(basis i)$j))`;;

(* ------------------------------------------------------------------------- *)
(* Invertible matrices (not assumed square, but it's vacuous otherwise).     *)
(* ------------------------------------------------------------------------- *)

let invertible = new_definition
  `invertible(A:real^N^M) <=>
        ?A':real^M^N. (A ** A' = mat 1) /\ (A' ** A = mat 1)`;;

let INVERTIBLE_I = `invertible(mat 1:real^N^N)`;;

let INVERTIBLE_NEG = `!A:real^N^M. invertible(--A) <=> invertible A`;;

let INVERTIBLE_CMUL = `!A:real^N^M c. invertible(c %% A) <=> ~(c = &0) /\ invertible(A)`;;

let INVERTIBLE_MAT = `!a. invertible(mat a:real^N^N) <=> ~(a = 0)`;;

let MATRIX_ENTIRE = `(!A:real^N^M B:real^P^N. invertible A ==> (A ** B = mat 0 <=> B = mat 0)) /\
   (!A:real^N^M B:real^P^N. invertible B ==> (A ** B = mat 0 <=> A = mat 0))`;;

(* ------------------------------------------------------------------------- *)
(* Correspondence between matrices and linear operators.                     *)
(* ------------------------------------------------------------------------- *)

let matrix = new_definition
  `(matrix:(real^M->real^N)->real^M^N) f = lambda i j. f(basis j)$i`;;

let MATRIX_COMPONENT = `!f:real^M->real^N i j.
        1 <= j /\ j <= dimindex(:M)
        ==> (matrix f)$i$j = f (basis j)$i`;;

let MATRIX_VECTOR_MUL_LINEAR = `!A:real^N^M. linear(\x. A ** x)`;;

let MATRIX_WORKS = `!f:real^M->real^N. linear f ==> !x. matrix f ** x = f(x)`;;

let MATRIX_VECTOR_MUL = `!f:real^M->real^N. linear f ==> f = \x. matrix f ** x`;;

let MATRIX_OF_MATRIX_VECTOR_MUL = `!A:real^N^M. matrix(\x. A ** x) = A`;;

let MATRIX_COMPOSE = `!f g. linear f /\ linear g ==> (matrix(g o f) = matrix g ** matrix f)`;;

let MATRIX_0 = `matrix(\x. vec 0):real^M^N = mat 0`;;

let MATRIX_VECTOR_COLUMN = `!A:real^N^M x.
        A ** x = vsum(1..dimindex(:N)) (\i. x$i % (transp A)$i)`;;

let MATRIX_MUL_COMPONENT = `!i. 1 <= i /\ i <= dimindex(:P)
       ==> ((A:real^N^P) ** (B:real^M^N))$i = transp B ** A$i`;;

let ADJOINT_MATRIX = `!A:real^N^M. adjoint(\x. A ** x) = (\x. transp A ** x)`;;

let MATRIX_ADJOINT = `!f. linear f ==> matrix(adjoint f) = transp(matrix f)`;;

let MATRIX_ID = `matrix(\x. x) = mat 1`;;

let MATRIX_I = `matrix I = mat 1`;;

let LINEAR_EQ_MATRIX = `!f g. linear f /\ linear g /\ matrix f = matrix g ==> f = g`;;

let MATRIX_CMUL = `!f:real^M->real^N c.
        linear f ==> matrix(\x. c % f x) = c %% matrix f`;;

let MATRIX_NEG = `!f:real^M->real^N.
        linear f ==> matrix(\x. --(f x)) = --(matrix f)`;;

let MATRIX_ADD = `!f g:real^M->real^N.
        linear f /\ linear g ==> matrix(\x. f x + g x) = matrix f + matrix g`;;

let MATRIX_SELF_ADJOINT = `!f. linear f ==> (adjoint f = f <=> symmetric_matrix(matrix f))`;;

let LINEAR_MATRIX_EXISTS = `!f:real^M->real^N. linear f <=> ?A:real^M^N. f = \x. A ** x`;;

let LINEAR_1_GEN = `!f:real^N->real^N.
        dimindex(:N) = 1 ==> (linear f <=> ?c. f = \x. c % x)`;;

let LINEAR_1 = `!f:real^1->real^1. linear f <=> ?c. f = \x. c % x`;;

let SYMMETRIC_MATRIX = `!A:real^N^N. symmetric_matrix A <=> adjoint(\x. A ** x) = \x. A ** x`;;

let DOT_MATRIX_TRANSP_LMUL = `!A x y:real^N. (transp A ** x) dot y = x dot (A ** y)`;;

let DOT_MATRIX_TRANSP_RMUL = `!A x y:real^N. x dot (transp A ** y) = (A ** x) dot y`;;

let SYMMETRIC_MATRIX_ORTHOGONAL_EIGENVECTORS = `!A:real^N^N v w a b.
        symmetric_matrix A /\ A ** v = a % v /\ A ** w = b % w /\ ~(a = b)
        ==> orthogonal v w`;;

let MATRIX_INJECTIVE_0 = `!m:real^M^N.
        (!x y:real^M. m ** x = m ** y ==> x = y) <=>
        (!x:real^M. m ** x = vec 0 ==> x = vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* Operator norm.                                                            *)
(* ------------------------------------------------------------------------- *)

let onorm = new_definition
 `onorm (f:real^M->real^N) = sup { norm(f x) | norm(x) = &1 }`;;

let NORM_BOUND_GENERALIZE = `!f:real^M->real^N b.
        linear f
        ==> ((!x. norm(x) = &1 ==> norm(f x) <= b) <=>
             (!x. norm(f x) <= b * norm(x)))`;;

let ONORM_DOT = `!f:real^M->real^N. onorm f = sup {f x dot y | norm x = &1 /\ norm y = &1}`;;

let ONORM = `!f:real^M->real^N.
        linear f
        ==> (!x. norm(f x) <= onorm f * norm(x)) /\
            (!b. (!x. norm(f x) <= b * norm(x)) ==> onorm f <= b)`;;

let ONORM_LE_EQ = `!f:real^M->real^N b.
        linear f ==> (onorm f <= b <=> !x. norm(f x) <= b * norm x)`;;

let ONORM_POS_LE = `!f. linear f ==> &0 <= onorm f`;;

let ONORM_EQ_0 = `!f:real^M->real^N. linear f ==> ((onorm f = &0) <=> (!x. f x = vec 0))`;;

let ONORM_CONST = `!y:real^N. onorm(\x:real^M. y) = norm(y)`;;

let ONORM_POS_LT = `!f. linear f ==> (&0 < onorm f <=> ~(!x. f x = vec 0))`;;

let ONORM_COMPOSE = `!f g. linear f /\ linear g ==> onorm(f o g) <= onorm f * onorm g`;;

let ONORM_CMUL = `!f:real^M->real^N c. linear f ==> onorm(\x. c % f x) = abs c * onorm f`;;

let ONORM_NEG = `!f:real^M->real^N. onorm(\x. --f x) = onorm f`;;

let ONORM_TRIANGLE = `!f:real^M->real^N g.
        linear f /\ linear g ==> onorm(\x. f x + g x) <= onorm f + onorm g`;;

let ONORM_TRIANGLE_LE = `!f g. linear f /\ linear g /\ onorm(f) + onorm(g) <= e
         ==> onorm(\x. f x + g x) <= e`;;

let ONORM_TRIANGLE_LT = `!f g. linear f /\ linear g /\ onorm(f) + onorm(g) < e
         ==> onorm(\x. f x + g x) < e`;;

let ONORM_ID = `onorm(\x:real^N. x) = &1`;;

let ONORM_I = `onorm(I:real^N->real^N) = &1`;;

let ONORM_INVERSE_FUNCTION_BOUND = `!f g:real^M->real^N.
        linear f /\ linear g /\ f o g = I ==> &1 <= onorm f * onorm g`;;

let ONORM_ADJOINT = `!f:real^N->real^N. linear f ==> onorm(adjoint f) = onorm f`;;

let ONORM_COMPOSE_ADJOINT_LEFT = `!f:real^N->real^N. linear f ==> onorm(adjoint f o f) = onorm f pow 2`;;

let ONORM_COMPOSE_ADJOINT_RIGHT = `!f:real^N->real^N. linear f ==> onorm(f o adjoint f) = onorm f pow 2`;;

let ONORM_TRANSP = `!A:real^N^N. onorm(\x. transp A ** x) = onorm(\x. A ** x)`;;

let ONORM_COVARIANCE = `!A:real^N^N.
        onorm(\x. (transp A ** A) ** x) = onorm(\x. A ** x) pow 2`;;

let ONORM_COVARIANCE_ALT = `!A:real^N^N.
        onorm(\x. (A ** transp A) ** x) = onorm(\x. A ** x) pow 2`;;

let ONORM_LE_EQ_2,ONORM_LE_EQ_2_ABS = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N b.
        linear f
        ==> (onorm f <= b <=> !x y. x dot (f y) <= b * norm x * norm y)) /\
   (!f:real^M->real^N b.
        linear f
        ==> (onorm f <= b <=> !x y. abs(x dot (f y)) <= b * norm x * norm y))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `linear(f:real^M->real^N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT
   `(r ==> q) /\ (p ==> r) /\ (q ==> p) ==> (p <=> q) /\ (p <=> r)`) THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[ONORM_LE_EQ]] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^M`] THEN
    TRANS_TAC REAL_LE_TRANS `norm(x:real^N) * norm((f:real^M->real^N) y)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `b * x * y:real = x * b * y`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL; NORM_POS_LE];
    X_GEN_TAC `x:real^M` THEN
    ASM_CASES_TAC `(f:real^M->real^N) x = vec 0` THENL
     [ASM_CASES_TAC `x:real^M = vec 0` THEN
      ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO; REAL_LE_REFL] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`basis 1:real^N`; `x:real^M`]) THEN
      ASM_SIMP_TAC[DOT_RZERO; NORM_BASIS; LE_REFL;
                   DIMINDEX_GE_1; REAL_MUL_LID];
      FIRST_ASSUM(MP_TAC o SPECL [`(f:real^M->real^N) x`; `x:real^M`]) THEN
      REWRITE_TAC[GSYM NORM_POW_2; REAL_ARITH
       `y pow 2 <= b * y * x <=> y * y <= y * b * x`] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; NORM_POS_LT]]]);;

(* ------------------------------------------------------------------------- *)
(* It's handy to "lift" from R to R^1 and "drop" from R^1 to R.              *)
(* ------------------------------------------------------------------------- *)

let lift = new_definition
 `(lift:real->real^1) x = lambda i. x`;;

let drop = new_definition
 `(drop:real^1->real) x = x$1`;;

let LIFT_COMPONENT = `!x. (lift x)$1 = x`;;

let LIFT_DROP = `(!x. lift(drop x) = x) /\ (!x. drop(lift x) = x)`;;

let IMAGE_LIFT_DROP = `(!s. IMAGE (lift o drop) s = s) /\ (!s. IMAGE (drop o lift) s = s)`;;

let IN_IMAGE_LIFT_DROP = `(!x s. x IN IMAGE lift s <=> drop x IN s) /\
   (!x s. x IN IMAGE drop s <=> lift x IN s)`;;

let FORALL_LIFT = `(!x. P x) = (!x. P(lift x))`;;

let EXISTS_LIFT = `(?x. P x) = (?x. P(lift x))`;;

let FORALL_DROP = `(!x. P x) = (!x. P(drop x))`;;

let EXISTS_DROP = `(?x. P x) = (?x. P(drop x))`;;

let FORALL_LIFT_FUN = `!P:(A->real^1)->bool. (!f. P f) <=> (!f. P(lift o f))`;;

let FORALL_DROP_FUN = `!P:(A->real)->bool. (!f. P f) <=> (!f. P(drop o f))`;;

let FORALL_FUN_LIFT = `!P:(real->A)->bool. (!f. P f) <=> (!f. P(f o lift))`;;

let FORALL_FUN_DROP = `!P:(real^1->A)->bool. (!f. P f) <=> (!f. P(f o drop))`;;

let EXISTS_LIFT_FUN = `!P:(A->real^1)->bool. (?f. P f) <=> (?f. P(lift o f))`;;

let EXISTS_DROP_FUN = `!P:(A->real)->bool. (?f. P f) <=> (?f. P(drop o f))`;;

let EXISTS_FUN_LIFT = `!P:(real->A)->bool. (?f. P f) <=> (?f. P(f o lift))`;;

let EXISTS_FUN_DROP = `!P:(real^1->A)->bool. (?f. P f) <=> (?f. P(f o drop))`;;

let LIFT_EQ = `!x y. (lift x = lift y) <=> (x = y)`;;

let DROP_EQ = `!x y. (drop x = drop y) <=> (x = y)`;;

let LIFT_IN_IMAGE_LIFT = `!x s. (lift x) IN (IMAGE lift s) <=> x IN s`;;

let FORALL_LIFT_IMAGE = `!P. (!s. P s) <=> (!s. P(IMAGE lift s))`;;

let EXISTS_LIFT_IMAGE = `!P. (?s. P s) <=> (?s. P(IMAGE lift s))`;;

let SUBSET_LIFT_IMAGE = `!s t. IMAGE lift s SUBSET IMAGE lift t <=> s SUBSET t`;;

let FORALL_DROP_IMAGE = `!P. (!s. P s) <=> (!s. P(IMAGE drop s))`;;

let EXISTS_DROP_IMAGE = `!P. (?s. P s) <=> (?s. P(IMAGE drop s))`;;

let SUBSET_DROP_IMAGE = `!s t. IMAGE drop s SUBSET IMAGE drop t <=> s SUBSET t`;;

let DROP_IN_IMAGE_DROP = `!x s. (drop x) IN (IMAGE drop s) <=> x IN s`;;

let LIFT_NUM = `!n. lift(&n) = vec n`;;

let LIFT_ADD = `!x y. lift(x + y) = lift x + lift y`;;

let LIFT_SUB = `!x y. lift(x - y) = lift x - lift y`;;

let LIFT_CMUL = `!x c. lift(c * x) = c % lift(x)`;;

let LIFT_NEG = `!x. lift(--x) = --(lift x)`;;

let LIFT_EQ_CMUL = `!x. lift x = x % vec 1`;;

let SUM_VSUM = `!f s. sum s f = drop(vsum s(lift o f))`;;

let VSUM_REAL = `!f s. vsum s f = lift(sum s (drop o f))`;;

let LIFT_SUM = `!k x. lift(sum k x) = vsum k (lift o x)`;;

let DROP_VSUM = `!k x. drop(vsum k x) = sum k (drop o x)`;;

let DROP_LAMBDA = `!x. drop(lambda i. x i) = x 1`;;

let DROP_VEC = `!n. drop(vec n) = &n`;;

let DROP_ADD = `!x y. drop(x + y) = drop x + drop y`;;

let DROP_SUB = `!x y. drop(x - y) = drop x - drop y`;;

let DROP_CMUL = `!x c. drop(c % x) = c * drop(x)`;;

let DROP_NEG = `!x. drop(--x) = --(drop x)`;;

let NORM_1 = `!x. norm x = abs(drop x)`;;

let DIST_1 = `!x y. dist(x,y) = abs(drop x - drop y)`;;

let NORM_1_POS = `!x. &0 <= drop x ==> norm x = drop x`;;

let NORM_LIFT = `!x. norm(lift x) = abs(x)`;;

let DIST_LIFT = `!x y. dist(lift x,lift y) = abs(x - y)`;;

let ABS_DROP = `!x. abs(drop x) = norm x`;;

let LINEAR_VMUL_DROP = `!f v. linear f ==> linear (\x. drop(f x) % v)`;;

let LINEAR_FROM_REALS = `!f:real^1->real^N. linear f ==> f = \x. drop x % column 1 (matrix f)`;;

let LINEAR_TO_REALS = `!f:real^N->real^1. linear f ==> f = \x. lift(row 1 (matrix f) dot x)`;;

let LINEAR_FROM_1 = `!f:real^1->real^N. linear f <=> ?c. f = \x. drop x % c`;;

let DROP_EQ_0 = `!x. drop x = &0 <=> x = vec 0`;;

let DROP_WLOG_LE = `(!x y. P x y <=> P y x) /\ (!x y. drop x <= drop y ==> P x y)
   ==> (!x y. P x y)`;;

let IMAGE_LIFT_UNIV = `IMAGE lift (:real) = (:real^1)`;;

let IMAGE_DROP_UNIV = `IMAGE drop (:real^1) = (:real)`;;

let LINEAR_LIFT_DOT = `!a. linear(\x. lift(a dot x))`;;

let LINEAR_TO_1 = `!f:real^N->real^1. linear f <=> ?a. f = \x. lift(a dot x)`;;

let LINEAR_LIFT_COMPONENT = `!k. linear(\x:real^N. lift(x$k))`;;

let BILINEAR_DROP_MUL = `bilinear (\x y:real^N. drop x % y)`;;

let BILINEAR_MUL_DROP = `bilinear(\y:real^N x. drop x % y)`;;

let BILINEAR_LIFT_MUL = `bilinear (\x y. lift(drop x * drop y))`;;

let LINEAR_COMPONENTWISE = `!f:real^M->real^N.
        linear f <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> linear(\x. lift(f(x)$i))`;;

let DROP_BASIS = `!i. drop(basis i) = if i = 1 then &1 else &0`;;

(* ------------------------------------------------------------------------- *)
(* Indicator (characteristic) functions into real^1.                         *)
(* ------------------------------------------------------------------------- *)

let indicator = new_definition
  `indicator s :real^M->real^1 = \x. if x IN s then vec 1 else vec 0`;;

let DROP_INDICATOR = `!s x. drop(indicator s x) = if x IN s then &1 else &0`;;

let DROP_INDICATOR_POS_LE = `!s x. &0 <= drop(indicator s x)`;;

let DROP_INDICATOR_LE_1 = `!s x. drop(indicator s x) <= &1`;;

let DROP_INDICATOR_ABS_LE_1 = `!s x. abs(drop(indicator s x)) <= &1`;;

let INDICATOR_COMPLEMENT = `!s. indicator((:real^N) DIFF s) = \x. vec 1 - indicator s x`;;

(* ------------------------------------------------------------------------- *)
(* Flattening and matrifying of arithmetic operations.                       *)
(* ------------------------------------------------------------------------- *)

let VECTORIZE_ADD = `!m1 m2:real^N^M. vectorize(m1 + m2) = vectorize m1 + vectorize m2`;;

let VECTORIZE_CMUL = `!c m:real^N^M. vectorize(c %% m) = c % vectorize m`;;

let VECTORIZE_SUB = `!m1 m2:real^N^M. vectorize(m1 - m2) = vectorize m1 - vectorize m2`;;

let VECTORIZE_0 = `vectorize(mat 0:real^N^M) = vec 0`;;

let MATRIFY_0 = `matrify(vec 0) = mat 0`;;

let VECTORIZE_EQ_0 = `!m:real^N^M. vectorize m = vec 0 <=> m = mat 0`;;

let MATRIFY_ADD = `!x y:real^(M,N)finite_prod. matrify(x + y) = matrify x + matrify y`;;

let MATRIFY_CMUL = `!c x:real^(M,N)finite_prod. matrify(c % x) = c %% matrify x`;;

let MATRIFY_SUB = `!x y:real^(M,N)finite_prod. matrify(x - y) = matrify x - matrify y`;;

let MATRIFY_EQ_0 = `!m:real^(M,N)finite_prod. matrify m = mat 0 <=> m = vec 0`;;

let BILINEAR_MATRIX_VECTOR_MUL = `bilinear (\(m:real^(M,N)finite_prod) x:real^N. matrify m ** x)`;;

let BILINEAR_MATRIX_MUL = `bilinear (\(m1:real^(M,N)finite_prod) (m2:real^(N,P)finite_prod).
                   vectorize(matrify m1 ** matrify m2))`;;

(* ------------------------------------------------------------------------- *)
(* Pasting vectors.                                                          *)
(* ------------------------------------------------------------------------- *)

let LINEAR_FSTCART = `linear fstcart`;;

let LINEAR_SNDCART = `linear sndcart`;;

let FSTCART_VEC = `!n. fstcart(vec n) = vec n`;;

let FSTCART_ADD = `!x:real^(M,N)finite_sum y. fstcart(x + y) = fstcart(x) + fstcart(y)`;;

let FSTCART_CMUL = `!x:real^(M,N)finite_sum c. fstcart(c % x) = c % fstcart(x)`;;

let FSTCART_NEG = `!x:real^(M,N)finite_sum. --(fstcart x) = fstcart(--x)`;;

let FSTCART_SUB = `!x:real^(M,N)finite_sum y. fstcart(x - y) = fstcart(x) - fstcart(y)`;;

let FSTCART_VSUM = `!k x. FINITE k ==> (fstcart(vsum k x) = vsum k (\i. fstcart(x i)))`;;

let SNDCART_VEC = `!n. sndcart(vec n) = vec n`;;

let SNDCART_ADD = `!x:real^(M,N)finite_sum y. sndcart(x + y) = sndcart(x) + sndcart(y)`;;

let SNDCART_CMUL = `!x:real^(M,N)finite_sum c. sndcart(c % x) = c % sndcart(x)`;;

let SNDCART_NEG = `!x:real^(M,N)finite_sum. --(sndcart x) = sndcart(--x)`;;

let SNDCART_SUB = `!x:real^(M,N)finite_sum y. sndcart(x - y) = sndcart(x) - sndcart(y)`;;

let SNDCART_VSUM = `!k x. FINITE k ==> (sndcart(vsum k x) = vsum k (\i. sndcart(x i)))`;;

let PASTECART_VEC = `!n. pastecart (vec n) (vec n) = vec n`;;

let PASTECART_ADD = `!x1 y1 x2:real^M y2:real^N.
     pastecart x1 y1 + pastecart x2 y2 = pastecart (x1 + x2) (y1 + y2)`;;

let PASTECART_CMUL = `!x1 y1 c. pastecart (c % x1) (c % y1) = c % pastecart x1 y1`;;

let PASTECART_NEG = `!x:real^M y:real^N. pastecart (--x) (--y) = --(pastecart x y)`;;

let PASTECART_SUB = `!x1 y1 x2:real^M y2:real^N.
     pastecart x1 y1 - pastecart x2 y2 = pastecart (x1 - x2) (y1 - y2)`;;

let PASTECART_VSUM = `!k x y. FINITE k ==> (pastecart (vsum k x) (vsum k y) =
                         vsum k (\i. pastecart (x i) (y i)))`;;

let PASTECART_EQ_VEC = `!x y n. pastecart x y = vec n <=> x = vec n /\ y = vec n`;;

let FSTCART_SNDCART_MAT_ZERO = `fstcart(mat 0:real^M^(A,B)finite_sum) = mat 0 /\
   sndcart(mat 0:real^M^(A,B)finite_sum) = mat 0`;;

let FSTCART_SNDCART_MATRIX_ADD = `!x:real^K^(M,N)finite_sum y.
     fstcart(x + y) = fstcart(x) + fstcart(y) /\
     sndcart(x + y) = sndcart(x) + sndcart(y)`;;

let NORM_FSTCART = `!x. norm(fstcart x) <= norm x`;;

let DIST_FSTCART = `!x y. dist(fstcart x,fstcart y) <= dist(x,y)`;;

let NORM_SNDCART = `!x. norm(sndcart x) <= norm x`;;

let DIST_SNDCART = `!x y. dist(sndcart x,sndcart y) <= dist(x,y)`;;

let DOT_PASTECART = `!x1 x2 y1 y2. (pastecart x1 x2) dot (pastecart y1 y2) =
                x1 dot y1 + x2 dot y2`;;

let SQNORM_PASTECART = `!x y. norm(pastecart x y) pow 2 = norm(x) pow 2 + norm(y) pow 2`;;

let NORM_PASTECART = `!x y. norm(pastecart x y) = sqrt(norm(x) pow 2 + norm(y) pow 2)`;;

let NORM_PASTECART_LE = `!x y. norm(pastecart x y) <= norm(x) + norm(y)`;;

let DIST_PASTECART_LE = `!x1 y1 x2 y2.
        dist(pastecart x1 y1,pastecart x2 y2)
        <= dist(x1,x2) + dist(y1,y2)`;;

let NORM_LE_PASTECART = `!x:real^M y:real^N.
    norm(x) <= norm(pastecart x y) /\
    norm(y) <= norm(pastecart x y)`;;

let DIST_LE_PASTECART = `!x1 y1 x2 y2.
        dist(x1,x2) <= dist(pastecart x1 y1,pastecart x2 y2) /\
        dist(y1,y2) <= dist(pastecart x1 y1,pastecart x2 y2)`;;

let NORM_PASTECART_0 = `(!x. norm(pastecart x (vec 0)) = norm x) /\
   (!y. norm(pastecart (vec 0) y) = norm y)`;;

let DIST_PASTECART_CANCEL = `(!x x' y. dist(pastecart x y,pastecart x' y) = dist(x,x')) /\
   (!x y y'. dist(pastecart x y,pastecart x y') = dist(y,y'))`;;

let LINEAR_PASTECART = `!f:real^M->real^N g:real^M->real^P.
        linear f /\ linear g ==> linear (\x. pastecart (f x) (g x))`;;

let LINEAR_PASTECART_EQ = `!f:real^M->real^N g:real^M->real^P.
        linear (\x. pastecart (f x) (g x)) <=> linear f /\ linear g`;;

(* ------------------------------------------------------------------------- *)
(* Drop the k'th coordinate, or insert t at the k'th coordinate.             *)
(* ------------------------------------------------------------------------- *)

let dropout = new_definition
  `(dropout k:real^M->real^N) x =
        lambda i. if i < k /\ i <= dimindex(:M) then x$i
                  else if i + 1 <= dimindex(:M) then x$(i + 1)
                  else &0`;;

let pushin = new_definition
 `pushin k t x = lambda i. if i < k then x$i
                           else if i = k then t
                           else x$(i - 1)`;;

let DROPOUT_PUSHIN = `!k t x.
        dimindex(:M) + 1 = dimindex(:N)
        ==> (dropout k:real^N->real^M) (pushin k t x) = x`;;

let PUSHIN_DROPOUT = `!k x.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> pushin k (x$k) ((dropout k:real^N->real^M) x) = x`;;

let DROPOUT_GALOIS = `!k x:real^N y:real^M.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (y = dropout k x <=> (?t. x = pushin k t y))`;;

let IN_IMAGE_DROPOUT = `!x s.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (x IN IMAGE (dropout k:real^N->real^M) s <=>
             ?t. (pushin k t x) IN s)`;;

let DROPOUT_EQ = `!x y k. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
           x$k = y$k /\ (dropout k:real^N->real^M) x = dropout k y
           ==> x = y`;;

let DROPOUT_0 = `dropout k (vec 0:real^N) = vec 0`;;

let DOT_DROPOUT = `!k x y:real^N.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (dropout k x:real^M) dot (dropout k y) = x dot y - x$k * y$k`;;

let DOT_PUSHIN = `!k a b x y:real^M.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (pushin k a x:real^N) dot (pushin k b y) = x dot y + a * b`;;

let DROPOUT_ADD = `!k x y:real^N. dropout k (x + y) = dropout k x + dropout k y`;;

let DROPOUT_SUB = `!k x y:real^N. dropout k (x - y) = dropout k x - dropout k y`;;

let DROPOUT_MUL = `!k c x:real^N. dropout k (c % x) = c % dropout k x`;;

let LINEAR_DROPOUT = `!k. linear(dropout k :real^N->real^M)`;;

let LINEAR_PUSHIN = `!k. linear(pushin k (&0))`;;

(* ------------------------------------------------------------------------- *)
(* A bit of linear algebra.                                                  *)
(* ------------------------------------------------------------------------- *)

let subspace = new_definition
 `subspace s <=>
        vec(0) IN s /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\
        (!c x. x IN s ==> (c % x) IN s)`;;

let span = new_definition
  `span s = subspace hull s`;;

let dependent = new_definition
 `dependent s <=> ?a. a IN s /\ a IN span(s DELETE a)`;;

let independent = new_definition
 `independent s <=> ~(dependent s)`;;

(* ------------------------------------------------------------------------- *)
(* Closure properties of subspaces.                                          *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_UNIV = `subspace(UNIV:real^N->bool)`;;

let SUBSPACE_IMP_NONEMPTY = `!s. subspace s ==> ~(s = {})`;;

let SUBSPACE_0 = `subspace s ==> vec(0) IN s`;;

let SUBSPACE_ADD = `!x y s. subspace s /\ x IN s /\ y IN s ==> (x + y) IN s`;;

let SUBSPACE_MUL = `!x c s. subspace s /\ x IN s ==> (c % x) IN s`;;

let SUBSPACE_MUL_EQ = `!s c x:real^N. subspace s ==> ((c % x) IN s <=> c = &0 \/ x IN s)`;;

let SUBSPACE_NEG = `!x s. subspace s /\ x IN s ==> (--x) IN s`;;

let SUBSPACE_NEG_EQ = `!s x:real^N. subspace s ==> (--x IN s <=> x IN s)`;;

let SUBSPACE_SUB = `!x y s. subspace s /\ x IN s /\ y IN s ==> (x - y) IN s`;;

let SUBSPACE_VSUM = `!s f t. subspace s /\ FINITE t /\ (!x. x IN t ==> f(x) IN s)
           ==> (vsum t f) IN s`;;

let SUBSPACE_LINEAR_IMAGE = `!f s. linear f /\ subspace s ==> subspace(IMAGE f s)`;;

let SUBSPACE_LINEAR_PREIMAGE = `!f s. linear f /\ subspace s ==> subspace {x | f(x) IN s}`;;

let SUBSPACE_TRIVIAL = `subspace {vec 0}`;;

let SUBSPACE_INTER = `!s t. subspace s /\ subspace t ==> subspace (s INTER t)`;;

let SUBSPACE_INTERS = `!f. (!s. s IN f ==> subspace s) ==> subspace(INTERS f)`;;

let LINEAR_INJECTIVE_0_SUBSPACE = `!f:real^M->real^N s.
        linear f /\ subspace s
         ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              (!x. x IN s /\ f x = vec 0 ==> x = vec 0))`;;

let SUBSPACE_UNION_CHAIN = `!s t:real^N->bool.
        subspace s /\ subspace t /\ subspace(s UNION t)
         ==> s SUBSET t \/ t SUBSET s`;;

let SUBSPACE_PCROSS = `!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t ==> subspace(s PCROSS t)`;;

let SUBSPACE_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        subspace(s PCROSS t) <=> subspace s /\ subspace t`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SPAN_SPAN = `!s. span(span s) = span s`;;

let SPAN_MONO = `!s t. s SUBSET t ==> span s SUBSET span t`;;

let SUBSPACE_SPAN = `!s. subspace(span s)`;;

let NONEMPTY_SPAN = `!s:real^N->bool. ~(span s = {})`;;

let SPAN_CLAUSES = `(!a s. a IN s ==> a IN span s) /\
   (vec(0) IN span s) /\
   (!x y s. x IN span s /\ y IN span s ==> (x + y) IN span s) /\
   (!x c s. x IN span s ==> (c % x) IN span s)`;;

let SPAN_INDUCT = `!s h. (!x. x IN s ==> x IN h) /\ subspace h ==> !x. x IN span(s) ==> h(x)`;;

let SPAN_EMPTY = `span {} = {vec 0}`;;

let INDEPENDENT_EMPTY = `independent {}`;;

let INDEPENDENT_NONZERO = `!s. independent s ==> ~(vec 0 IN s)`;;

let INDEPENDENT_MONO = `!s t. independent t /\ s SUBSET t ==> independent s`;;

let DEPENDENT_MONO = `!s t:real^N->bool. dependent s /\ s SUBSET t ==> dependent t`;;

let SPAN_SUBSPACE = `!b s. b SUBSET s /\ s SUBSET (span b) /\ subspace s ==> (span b = s)`;;

let SPAN_INDUCT_ALT = `!s h. h(vec 0) /\
         (!c x y. x IN s /\ h(y) ==> h(c % x + y))
          ==> !x:real^N. x IN span(s) ==> h(x)`;;

(* ------------------------------------------------------------------------- *)
(* Individual closure properties.                                            *)
(* ------------------------------------------------------------------------- *)

let SPAN_SUPERSET = `!x. x IN s ==> x IN span s`;;

let SPAN_INC = `!s. s SUBSET span s`;;

let SPAN_UNION_SUBSET = `!s t. span s UNION span t SUBSET span(s UNION t)`;;

let SPAN_UNIV = `span(:real^N) = (:real^N)`;;

let SPAN_0 = `vec(0) IN span s`;;

let SPAN_ADD = `!x y s. x IN span s /\ y IN span s ==> (x + y) IN span s`;;

let SPAN_MUL = `!x c s. x IN span s ==> (c % x) IN span s`;;

let SPAN_MUL_EQ = `!x:real^N c s. ~(c = &0) ==> ((c % x) IN span s <=> x IN span s)`;;

let SPAN_NEG = `!x s. x IN span s ==> (--x) IN span s`;;

let SPAN_NEG_EQ = `!x s. --x IN span s <=> x IN span s`;;

let SPAN_SUB = `!x y s. x IN span s /\ y IN span s ==> (x - y) IN span s`;;

let SPAN_VSUM = `!s f t. FINITE t /\ (!x. x IN t ==> f(x) IN span(s))
           ==> (vsum t f) IN span(s)`;;

let SPAN_ADD_EQ = `!s x y. x IN span s ==> ((x + y) IN span s <=> y IN span s)`;;

let SPAN_EQ_SELF = `!s. span s = s <=> subspace s`;;

let SPAN_OF_SUBSPACE = `!s:real^N->bool. subspace s ==> span s = s`;;

let SPAN_SUBSET_SUBSPACE = `!s t:real^N->bool. s SUBSET t /\ subspace t ==> span s SUBSET t`;;

let SUBSPACE_TRANSLATION_SELF = `!s a. subspace s /\ a IN s ==> IMAGE (\x. a + x) s = s`;;

let SUBSPACE_TRANSLATION_SELF_EQ = `!s a:real^N. subspace s ==> (IMAGE (\x. a + x) s = s <=> a IN s)`;;

let SUBSPACE_SUMS = `!s t. subspace s /\ subspace t
         ==> subspace {x + y | x IN s /\ y IN t}`;;

let SPAN_UNION = `!s t. span(s UNION t) = {x + y:real^N | x IN span s /\ y IN span t}`;;

(* ------------------------------------------------------------------------- *)
(* Mapping under linear image.                                               *)
(* ------------------------------------------------------------------------- *)

let SPAN_LINEAR_IMAGE = `!f:real^M->real^N s. linear f ==> (span(IMAGE f s) = IMAGE f (span s))`;;

let DEPENDENT_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (dependent(IMAGE f s) <=> dependent s)`;;

let DEPENDENT_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        dependent(s)
        ==> dependent(IMAGE f s)`;;

let INDEPENDENT_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (independent(IMAGE f s) <=> independent s)`;;

(* ------------------------------------------------------------------------- *)
(* The key breakdown property.                                               *)
(* ------------------------------------------------------------------------- *)

let SPAN_BREAKDOWN = `!b s a:real^N.
      b IN s /\ a IN span s ==> ?k. (a - k % b) IN span(s DELETE b)`;;

let SPAN_BREAKDOWN_EQ = `!a:real^N s. (x IN span(a INSERT s) <=> (?k. (x - k % a) IN span s))`;;

let SPAN_INSERT_0 = `!s. span(vec 0 INSERT s) = span s`;;

let SPAN_SING = `!a. span {a} = {u % a | u IN (:real)}`;;

let SPAN_2 = `!a b. span {a,b} = {u % a + v % b | u IN (:real) /\ v IN (:real)}`;;

let SPAN_3 = `!a b c. span {a,b,c} =
      {u % a + v % b + w % c | u IN (:real) /\ v IN (:real) /\ w IN (:real)}`;;

(* ------------------------------------------------------------------------- *)
(* Hence some "reversal" results.                                            *)
(* ------------------------------------------------------------------------- *)

let IN_SPAN_INSERT = `!a b:real^N s.
        a IN span(b INSERT s) /\ ~(a IN span s) ==> b IN span(a INSERT s)`;;

let IN_SPAN_DELETE = `!a b s.
         a IN span s /\ ~(a IN span (s DELETE b))
         ==> b IN span (a INSERT (s DELETE b))`;;

let EQ_SPAN_INSERT_EQ = `!s x y:real^N. (x - y) IN span s ==> span(x INSERT s) = span(y INSERT s)`;;

(* ------------------------------------------------------------------------- *)
(* An explicit expansion is sometimes needed.                                *)
(* ------------------------------------------------------------------------- *)

let SPAN_EXPLICIT = `!(p:real^N -> bool).
        span p =
         {y | ?s u. FINITE s /\ s SUBSET p /\
                    vsum s (\v. u v % v) = y}`;;

let DEPENDENT_EXPLICIT = `!p. dependent (p:real^N -> bool) <=>
                ?s u. FINITE s /\ s SUBSET p /\
                      (?v. v IN s /\ ~(u v = &0)) /\
                      vsum s (\v. u v % v) = vec 0`;;

let DEPENDENT_FINITE = `!s:real^N->bool.
        FINITE s
        ==> (dependent s <=> ?u. (?v. v IN s /\ ~(u v = &0)) /\
                                 vsum s (\v. u(v) % v) = vec 0)`;;

let SPAN_FINITE = `!s:real^N->bool.
        FINITE s ==> span s = {y | ?u. vsum s (\v. u v % v) = y}`;;

(* ------------------------------------------------------------------------- *)
(* Standard bases are a spanning set, and obviously finite.                  *)
(* ------------------------------------------------------------------------- *)

let SPAN_STDBASIS = `span {basis i :real^N | 1 <= i /\ i <= dimindex(:N)} = UNIV`;;

let HAS_SIZE_STDBASIS = `{basis i :real^N | 1 <= i /\ i <= dimindex(:N)} HAS_SIZE
        dimindex(:N)`;;

let FINITE_STDBASIS = `FINITE {basis i :real^N | 1 <= i /\ i <= dimindex(:N)}`;;

let CARD_STDBASIS = `CARD {basis i :real^N | 1 <= i /\ i <= dimindex(:N)} =
        dimindex(:N)`;;

let IN_SPAN_IMAGE_BASIS = `!x:real^N s.
        x IN span(IMAGE basis s) <=>
          !i. 1 <= i /\ i <= dimindex(:N) /\ ~(i IN s) ==> x$i = &0`;;

let INDEPENDENT_STDBASIS = `independent {basis i :real^N | 1 <= i /\ i <= dimindex(:N)}`;;

let INDEPENDENT_BASIS_IMAGE = `!k. independent(IMAGE basis k:real^N->bool) <=> k SUBSET 1..dimindex(:N) `;;

(* ------------------------------------------------------------------------- *)
(* Definition of dimension, and setup of matroid for Euclidean span.         *)
(* ------------------------------------------------------------------------- *)

let dim = new_definition
  `dim (v:real^N->bool) =
   @n. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\ b HAS_SIZE n`;;

let euclidean_matroid = new_definition
 `euclidean_matroid = matroid((:real^N),span)`;;

let EUCLIDEAN_MATROID = `matroid_set euclidean_matroid = (:real^N) /\
   matroid_span euclidean_matroid = (span:(real^N->bool)->(real^N->bool))`;;

let EUCLIDEAN_MATROID_INDEPENDENT = `matroid_independent (euclidean_matroid:(real^N)matroid) = independent`;;

let EUCLIDEAN_MATROID_SPANNING = `!s. matroid_spanning euclidean_matroid s <=> span s = (:real^N)`;;

let EUCLIDEAN_MATROID_SUBSPACE = `matroid_subspace (euclidean_matroid:(real^N)matroid) = subspace`;;

let EUCLIDEAN_MATROID_FINITE_DIMENSIONAL = `matroid_finite_dimensional (euclidean_matroid:(real^N)matroid)`;;

let EUCLIDEAN_MATROID_DIMENSION = `matroid_dimension (euclidean_matroid:(real^N)matroid) = dimindex(:N)`;;

let EUCLIDEAN_MATROID_FINITE_DIM = `!s:real^N->bool. matroid_finite_dim euclidean_matroid s`;;

let EUCLIDEAN_SUBMATROID = `(!s:real^N->bool. matroid_set (submatroid euclidean_matroid s) = span s) /\
   (!s:real^N->bool. matroid_span (submatroid euclidean_matroid s) = span)`;;

let EUCLIDEAN_MATROID_DIM = `matroid_dim (euclidean_matroid:(real^N)matroid) = dim`;;

(* ------------------------------------------------------------------------- *)
(* Some linear algebra basics, leaning on matroids in many cases             *)
(* ------------------------------------------------------------------------- *)

let SPAN_EQ = `!s t:real^N->bool. span s = span t <=> s SUBSET span t /\ t SUBSET span s`;;

let SPAN_EQ_INSERT = `!s x:real^N. span(x INSERT s) = span s <=> x IN span s`;;

let INDEPENDENT_INSERT = `!a:real^N s. independent(a INSERT s) <=>
                  if a IN s then independent s
                  else independent s /\ ~(a IN span s)`;;

let SPAN_TRANS = `!x y:real^N s. x IN span(s) /\ y IN span(x INSERT s) ==> y IN span(s)`;;

let SPANNING_SUBSET_INDEPENDENT = `!s t:real^N->bool.
        t SUBSET s /\ independent s /\ s SUBSET span(t) ==> s = t`;;

let EXCHANGE_LEMMA = `!s t:real^N->bool.
        FINITE t /\ independent s /\ s SUBSET span t
        ==> ?t'. t' HAS_SIZE (CARD t) /\
                 s SUBSET t' /\ t' SUBSET (s UNION t) /\ s SUBSET (span t')`;;

let INDEPENDENT_SPAN_BOUND = `!s t. FINITE t /\ independent s /\ s SUBSET span(t)
         ==> FINITE s /\ CARD(s) <= CARD(t)`;;

let INDEPENDENT_BOUND = `!s:real^N->bool.
        independent s ==> FINITE s /\ CARD(s) <= dimindex(:N)`;;

let DEPENDENT_BIGGERSET = `!s:real^N->bool. (FINITE s ==> CARD(s) > dimindex(:N)) ==> dependent s`;;

let INDEPENDENT_IMP_FINITE = `!s:real^N->bool. independent s ==> FINITE s`;;

let MAXIMAL_INDEPENDENT_SUBSET_EXTEND = `!s v:real^N->bool.
        s SUBSET v /\ independent s
        ==> ?b. s SUBSET b /\ b SUBSET v /\ independent b /\
                v SUBSET (span b)`;;

let MAXIMAL_INDEPENDENT_SUBSET = `!v:real^N->bool. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b)`;;

let BASIS_EXISTS = `!v. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\
           b HAS_SIZE (dim v)`;;

let BASIS_EXISTS_FINITE = `!v. ?b. FINITE b /\
           b SUBSET v /\
           independent b /\
           v SUBSET (span b) /\
           b HAS_SIZE (dim v)`;;

let BASIS_SUBSPACE_EXISTS = `!s:real^N->bool.
        subspace s
        ==> ?b. FINITE b /\
                b SUBSET s /\
                independent b /\
                span b = s /\
                b HAS_SIZE dim s`;;

let INDEPENDENT_CARD_LE_DIM = `!v b:real^N->bool.
        b SUBSET v /\ independent b ==> FINITE b /\ CARD(b) <= dim v`;;

let SPAN_CARD_GE_DIM = `!v b:real^N->bool.
        v SUBSET (span b) /\ FINITE b ==> dim(v) <= CARD(b)`;;

let BASIS_CARD_EQ_DIM = `!v b. b SUBSET v /\ v SUBSET (span b) /\ independent b
         ==> FINITE b /\ (CARD b = dim v)`;;

let BASIS_HAS_SIZE_DIM = `!v b. independent b /\ span b = v ==> b HAS_SIZE (dim v)`;;

let DIM_SPAN = `!s:real^N->bool. dim(span s) = dim s`;;

let DIM_UNIQUE = `!v b. b SUBSET v /\ v SUBSET (span b) /\ independent b /\ b HAS_SIZE n
         ==> dim v = n`;;

let DIM_LE_CARD = `!s. FINITE s ==> dim s <= CARD s`;;

let DIM_UNIV = `dim(:real^N) = dimindex(:N)`;;

let DIM_SUBSET = `!s t:real^N->bool. s SUBSET t ==> dim(s) <= dim(t)`;;

let DIM_SUBSET_UNIV = `!s:real^N->bool. dim(s) <= dimindex(:N)`;;

let BASIS_HAS_SIZE_UNIV = `!b. independent b /\ span b = (:real^N) ==> b HAS_SIZE (dimindex(:N))`;;

let CARD_GE_DIM_INDEPENDENT = `!v b:real^N->bool.
        b SUBSET v /\ independent b /\ dim v <= CARD(b)
        ==> v SUBSET span b`;;

let CARD_LE_DIM_SPANNING = `!v b:real^N->bool.
        v SUBSET span b /\ FINITE b /\ CARD(b) <= dim v ==> independent b`;;

let CARD_EQ_DIM = `!v b. b SUBSET v /\ b HAS_SIZE (dim v)
         ==> (independent b <=> v SUBSET (span b))`;;

let INDEPENDENT_BOUND_GENERAL = `!s:real^N->bool. independent s ==> FINITE s /\ CARD(s) <= dim(s)`;;

let DEPENDENT_BIGGERSET_GENERAL = `!s:real^N->bool. (FINITE s ==> CARD(s) > dim(s)) ==> dependent s`;;

let DIM_INSERT_0 = `!s:real^N->bool. dim(vec 0 INSERT s) = dim s`;;

let DIM_EQ_CARD = `!s:real^N->bool. independent s ==> dim s = CARD s`;;

let DEPENDENT_EQ_DIM_LT_CARD = `!s:real^N->bool. dependent s <=> FINITE s ==> dim s < CARD s`;;

let INDEPENDENT_EQ_DIM_EQ_CARD = `!s:real^N->bool. independent s <=> FINITE s /\ dim s = CARD s`;;

let SUBSET_LE_DIM = `!s t:real^N->bool. s SUBSET (span t) ==> dim s <= dim t`;;

let SPAN_EQ_DIM = `!s t. span s = span t ==> dim s = dim t`;;

let DIM_EMPTY = `dim({}:real^N->bool) = 0`;;

let DIM_INSERT = `!x:real^N s. dim(x INSERT s) = if x IN span s then dim s else dim s + 1`;;

let CHOOSE_SUBSPACE_OF_SUBSPACE = `!s:real^N->bool n.
        n <= dim s ==> ?t. subspace t /\ t SUBSET span s /\ dim t = n`;;

let SUBSPACE_EXISTS = `!n. n <= dimindex(:N) ==> ?s:real^N->bool. subspace s /\ dim s = n`;;

let DIM_EQ_SPAN = `!s t:real^N->bool. s SUBSET t /\ dim t <= dim s ==> span s = span t`;;

let DIM_EQ_FULL = `!s:real^N->bool. dim s = dimindex(:N) <=> span s = (:real^N)`;;

let DIM_PSUBSET = `!s t:real^N->bool. span s PSUBSET span t ==> dim s < dim t`;;

let LOWDIM_EXPAND_DIMENSION = `!s:real^N->bool n.
        dim s <= n /\ n <= dimindex(:N)
        ==> ?t. dim(t) = n /\ span s SUBSET span t`;;

let LOWDIM_EXPAND_BASIS = `!s:real^N->bool n.
        dim s <= n /\ n <= dimindex(:N)
        ==> ?b. b HAS_SIZE n /\ independent b /\ span s SUBSET span b`;;

(* ------------------------------------------------------------------------- *)
(* Explicit formulation of independence.                                     *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_EXPLICIT = `!b:real^N->bool.
        independent b <=>
            FINITE b /\
            !c. vsum b (\v. c(v) % v) = vec 0 ==> !v. v IN b ==> c(v) = &0`;;

let INDEPENDENT_SING = `!x. independent {x} <=> ~(x = vec 0)`;;

let DEPENDENT_SING = `!x. dependent {x} <=> x = vec 0`;;

let DEPENDENT_2 = `!a b:real^N.
        dependent {a,b} <=>
                if a = b then a = vec 0
                else ?x y. x % a + y % b = vec 0 /\ ~(x = &0 /\ y = &0)`;;

let DEPENDENT_3 = `!a b c:real^N.
        ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> (dependent {a,b,c} <=>
             ?x y z. x % a + y % b + z % c = vec 0 /\
                     ~(x = &0 /\ y = &0 /\ z = &0))`;;

let INDEPENDENT_2 = `!a b:real^N x y.
        independent{a,b} /\ ~(a = b)
        ==> (x % a + y % b = vec 0 <=> x = &0 /\ y = &0)`;;

let INDEPENDENT_3 = `!a b c:real^N x y z.
        independent{a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> (x % a + y % b + z % c = vec 0 <=> x = &0 /\ y = &0 /\ z = &0)`;;

(* ------------------------------------------------------------------------- *)
(* A kind of closed graph property for linearity.                            *)
(* ------------------------------------------------------------------------- *)

let LINEAR_SUBSPACE_GRAPH = `!f:real^M->real^N.
        linear f <=> subspace {pastecart x (f x) | x IN (:real^M)}`;;

let SPANS_IMAGE = `!f b v. linear f /\ v SUBSET (span b)
           ==> (IMAGE f v) SUBSET span(IMAGE f b)`;;

let DIM_LINEAR_IMAGE_LE = `!f:real^M->real^N s. linear f ==> dim(IMAGE f s) <= dim s`;;

(* ------------------------------------------------------------------------- *)
(* Some stepping theorems.                                                   *)
(* ------------------------------------------------------------------------- *)

let DIM_SING = `!x. dim{x} = if x = vec 0 then 0 else 1`;;

let DIM_EQ_0 = `!s:real^N->bool. dim s = 0 <=> s SUBSET {vec 0}`;;

(* ------------------------------------------------------------------------- *)
(* Relation between bases and injectivity/surjectivity of map.               *)
(* ------------------------------------------------------------------------- *)

let SPANNING_SURJECTIVE_IMAGE = `!f:real^M->real^N s.
        UNIV SUBSET (span s) /\ linear f /\ (!y. ?x. f(x) = y)
        ==> UNIV SUBSET span(IMAGE f s)`;;

let INDEPENDENT_INJECTIVE_IMAGE_GEN = `!f:real^M->real^N s.
        independent s /\ linear f /\
        (!x y. x IN span s /\ y IN span s /\ f(x) = f(y) ==> x = y)
        ==> independent (IMAGE f s)`;;

let INDEPENDENT_INJECTIVE_IMAGE = `!f:real^M->real^N s.
        independent s /\ linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> independent (IMAGE f s)`;;

(* ------------------------------------------------------------------------- *)
(* Picking an orthogonal replacement for a spanning set.                     *)
(* ------------------------------------------------------------------------- *)

let VECTOR_SUB_PROJECT_ORTHOGONAL = `!b:real^N x. b dot (x - ((b dot x) / (b dot b)) % b) = &0`;;

let BASIS_ORTHOGONAL = `!b:real^N->bool.
        FINITE b
        ==> ?c. FINITE c /\ CARD c <= CARD b /\
                span c = span b /\ pairwise orthogonal c`;;

let ORTHOGONAL_BASIS_EXISTS = `!v:real^N->bool.
        ?b. independent b /\
            b SUBSET span v /\
            v SUBSET span b /\
            b HAS_SIZE dim v /\
            pairwise orthogonal b`;;

let SPAN_SPECIAL_SCALE = `!s a x:real^N.
     span((a % x) INSERT s) = if a = &0 then span s else span(x INSERT s)`;;

(* ------------------------------------------------------------------------- *)
(* We can extend a linear basis-basis injection to the whole set.            *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INDEP_IMAGE_LEMMA = `!f b. linear(f:real^M->real^N) /\
         FINITE b /\
         independent (IMAGE f b) /\
         (!x y. x IN b /\ y IN b /\ (f x = f y) ==> (x = y))
         ==> !x. x IN span b ==> (f(x) = vec 0) ==> (x = vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* We can extend a linear mapping from basis.                                *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INDEPENDENT_EXTEND_LEMMA = `!f b. FINITE b
         ==> independent b
             ==> ?g:real^M->real^N.
                        (!x y. x IN span b /\ y IN span b
                                ==> (g(x + y) = g(x) + g(y))) /\
                        (!x c. x IN span b ==> (g(c % x) = c % g(x))) /\
                        (!x. x IN b ==> (g x = f x))`;;

let LINEAR_INDEPENDENT_EXTEND = `!f b. independent b
         ==> ?g:real^M->real^N. linear g /\ (!x. x IN b ==> (g x = f x))`;;

(* ------------------------------------------------------------------------- *)
(* Linear functions are equal on a subspace if they are on a spanning set.   *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_KERNEL = `!f. linear f ==> subspace {x | f(x) = vec 0}`;;

let LINEAR_EQ_0_SPAN = `!f:real^M->real^N b.
        linear f /\ (!x. x IN b ==> f(x) = vec 0)
        ==> !x. x IN span(b) ==> f(x) = vec 0`;;

let LINEAR_EQ_0 = `!f b s. linear f /\ s SUBSET (span b) /\ (!x. x IN b ==> f(x) = vec 0)
           ==> !x. x IN s ==> f(x) = vec 0`;;

let LINEAR_EQ = `!f g b s. linear f /\ linear g /\ s SUBSET (span b) /\
             (!x. x IN b ==> f(x) = g(x))
              ==> !x. x IN s ==> f(x) = g(x)`;;

let LINEAR_EQ_STDBASIS = `!f:real^M->real^N g.
        linear f /\ linear g /\
        (!i. 1 <= i /\ i <= dimindex(:M)
             ==> f(basis i) = g(basis i))
        ==> f = g`;;

let SUBSPACE_LINEAR_FIXED_POINTS = `!f:real^N->real^N. linear f ==> subspace {x | f(x) = x}`;;

(* ------------------------------------------------------------------------- *)
(* Similar results for bilinear functions.                                   *)
(* ------------------------------------------------------------------------- *)

let BILINEAR_EQ = `!f:real^M->real^N->real^P g b c s.
        bilinear f /\ bilinear g /\
        s SUBSET (span b) /\ t SUBSET (span c) /\
        (!x y. x IN b /\ y IN c ==> f x y = g x y)
         ==> !x y. x IN s /\ y IN t ==> f x y = g x y`;;

let BILINEAR_EQ_STDBASIS = `!f:real^M->real^N->real^P g.
        bilinear f /\ bilinear g /\
        (!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N)
             ==> f (basis i) (basis j) = g (basis i) (basis j))
        ==> f = g`;;

(* ------------------------------------------------------------------------- *)
(* Detailed theorems about left and right invertibility in general case.     *)
(* ------------------------------------------------------------------------- *)

let LEFT_INVERTIBLE_TRANSP = `!A:real^N^M.
    (?B:real^N^M. B ** transp A = mat 1) <=> (?B:real^M^N. A ** B = mat 1)`;;

let RIGHT_INVERTIBLE_TRANSP = `!A:real^N^M.
    (?B:real^N^M. transp A ** B = mat 1) <=> (?B:real^M^N. B ** A = mat 1)`;;

let INVERTIBLE_TRANSP = `!A:real^N^M. invertible(transp A) <=> invertible A`;;

let LINEAR_INJECTIVE_LEFT_INVERSE = `!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?g. linear g /\ g o f = I`;;

let LINEAR_INJECTIVE_LEFT_INVERSE_EQ = `!f:real^M->real^N.
        linear f
        ==> ((!x y. f x = f y ==> x = y) <=> ?g. linear g /\ g o f = I)`;;

let LINEAR_SURJECTIVE_RIGHT_INVERSE = `!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y) ==> ?g. linear g /\ f o g = I`;;

let LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ = `!f:real^M->real^N.
        linear f
        ==> ((!y. ?x. f x = y) <=> ?g. linear g /\ f o g = I)`;;

let MATRIX_LEFT_INVERTIBLE_INJECTIVE = `!A:real^N^M.
        (?B:real^M^N. B ** A = mat 1) <=>
        !x y:real^N. A ** x = A ** y ==> x = y`;;

let MATRIX_LEFT_INVERTIBLE_KER = `!A:real^N^M.
        (?B:real^M^N. B ** A = mat 1) <=> !x. A ** x = vec 0 ==> x = vec 0`;;

let MATRIX_RIGHT_INVERTIBLE_SURJECTIVE = `!A:real^N^M.
        (?B:real^M^N. A ** B = mat 1) <=> !y:real^M. ?x. A ** x = y`;;

let MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS = `!A:real^N^M. (?B:real^M^N. B ** A = mat 1) <=>
                !c. vsum(1..dimindex(:N)) (\i. c(i) % column i A) = vec 0 ==>
                    !i. 1 <= i /\ i <= dimindex(:N) ==> c(i) = &0`;;

let MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS = `!A:real^N^M. (?B:real^M^N. A ** B = mat 1) <=>
                !c. vsum(1..dimindex(:M)) (\i. c(i) % row i A) = vec 0 ==>
                    !i. 1 <= i /\ i <= dimindex(:M) ==> c(i) = &0`;;

let MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS = `!A:real^N^M. (?B:real^M^N. A ** B = mat 1) <=> span(columns A) = (:real^M)`;;

let MATRIX_LEFT_INVERTIBLE_SPAN_ROWS = `!A:real^N^M. (?B:real^M^N. B ** A = mat 1) <=> span(rows A) = (:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* An injective map real^N->real^N is also surjective.                       *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INJECTIVE_IMP_SURJECTIVE = `!f:real^N->real^N.
        linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> !y. ?x. f(x) = y`;;

(* ------------------------------------------------------------------------- *)
(* And vice versa.                                                           *)
(* ------------------------------------------------------------------------- *)

let LINEAR_SURJECTIVE_IMP_INJECTIVE = `!f:real^N->real^N.
        linear f /\ (!y. ?x. f(x) = y)
        ==> !x y. (f(x) = f(y)) ==> (x = y)`;;

let LINEAR_SURJECTIVE_IFF_INJECTIVE = `!f:real^N->real^N.
      linear f ==> ((!y. ?x. f x = y) <=> (!x y. f x = f y ==> x = y))`;;

(* ------------------------------------------------------------------------- *)
(* Hence either is enough for isomorphism.                                   *)
(* ------------------------------------------------------------------------- *)

let LEFT_RIGHT_INVERSE_EQ = `!f:A->A g h. f o g = I /\ g o h = I ==> f = h`;;

let ISOMORPHISM_EXPAND = `!f g. f o g = I /\ g o f = I <=> (!x. f(g x) = x) /\ (!x. g(f x) = x)`;;

let LINEAR_INJECTIVE_ISOMORPHISM = `!f:real^N->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)`;;

let LINEAR_SURJECTIVE_ISOMORPHISM = `!f:real^N->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)`;;

(* ------------------------------------------------------------------------- *)
(* Left and right inverses are the same for R^N->R^N.                        *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INVERSE_LEFT = `!f:real^N->real^N f'.
        linear f /\ linear f' ==> ((f o f' = I) <=> (f' o f = I))`;;

(* ------------------------------------------------------------------------- *)
(* Moreover, a one-sided inverse is automatically linear.                    *)
(* ------------------------------------------------------------------------- *)

let LEFT_INVERSE_LINEAR = `!f g:real^N->real^N. linear f /\ (g o f = I) ==> linear g`;;

let RIGHT_INVERSE_LINEAR = `!f g:real^N->real^N. linear f /\ (f o g = I) ==> linear g`;;

(* ------------------------------------------------------------------------- *)
(* Without (ostensible) constraints on types, though dimensions must match.  *)
(* ------------------------------------------------------------------------- *)

let LEFT_RIGHT_INVERSE_LINEAR = `!f g:real^M->real^N.
        linear f /\ g o f = I /\ f o g = I ==> linear g`;;

let LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE = `!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> ?g. linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y)`;;

let LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ = `!f:real^M->real^N.
        linear f
        ==> ((!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y) <=>
             ?g. linear g /\ f o g = I /\ g o f = I)`;;

let LINEAR_INJECTIVE_LEFT_RIGHT_INVERSE_EQ = `!f:real^N->real^N.
        linear f
        ==> ((!x y. f x = f y ==> x = y) <=>
             (?g. linear g /\ f o g = I /\ g o f = I))`;;

let LINEAR_SURJECTIVE_LEFT_RIGHT_INVERSE_EQ = `!f:real^N->real^N.
        linear f
        ==> ((!y. ?x. f x = y) <=>
             (?g. linear g /\ f o g = I /\ g o f = I))`;;

(* ------------------------------------------------------------------------- *)
(* The same result in terms of square matrices.                              *)
(* ------------------------------------------------------------------------- *)

let MATRIX_LEFT_RIGHT_INVERSE = `!A:real^N^N A':real^N^N. (A ** A' = mat 1) <=> (A' ** A = mat 1)`;;

(* ------------------------------------------------------------------------- *)
(* Invertibility of matrices and corresponding linear functions.             *)
(* ------------------------------------------------------------------------- *)

let MATRIX_LEFT_INVERTIBLE = `!f:real^M->real^N.
    linear f ==> ((?B:real^N^M. B ** matrix f = mat 1) <=>
                  (?g. linear g /\ g o f = I))`;;

let MATRIX_RIGHT_INVERTIBLE = `!f:real^M->real^N.
    linear f ==> ((?B:real^N^M. matrix f ** B = mat 1) <=>
                  (?g. linear g /\ f o g = I))`;;

let INVERTIBLE_LEFT_INVERSE = `!A:real^N^N. invertible(A) <=> ?B:real^N^N. B ** A = mat 1`;;

let INVERTIBLE_RIGHT_INVERSE = `!A:real^N^N. invertible(A) <=> ?B:real^N^N. A ** B = mat 1`;;

let MATRIX_INVERTIBLE = `!f:real^M->real^N.
        linear f
        ==> (invertible(matrix f) <=>
             ?g. linear g /\ f o g = I /\ g o f = I)`;;

let INVERTIBLE_EQ_INJECTIVE_AND_SURJECTIVE = `!m:real^M^N.
        invertible m <=>
        (!x y:real^M. m ** x = m ** y ==> x = y) /\
        IMAGE (\x. m ** x) (:real^M) = (:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* Left-invertible linear transformation has a lower bound.                  *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INVERTIBLE_BOUNDED_BELOW_POS = `!f:real^M->real^N g.
        linear f /\ linear g /\ (g o f = I)
        ==> ?B. &0 < B /\ !x. B * norm(x) <= norm(f x)`;;

let LINEAR_INVERTIBLE_BOUNDED_BELOW = `!f:real^M->real^N g.
        linear f /\ linear g /\ (g o f = I)
        ==> ?B. !x. B * norm(x) <= norm(f x)`;;

let LINEAR_INJECTIVE_BOUNDED_BELOW_POS = `!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?B. &0 < B /\ !x. norm(x) * B <= norm(f x)`;;

(* ------------------------------------------------------------------------- *)
(* Preservation of dimension by injective map.                               *)
(* ------------------------------------------------------------------------- *)

let DIM_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) ==> dim(IMAGE f s) = dim s`;;

let LINEAR_INJECTIVE_DIMINDEX_LE = `!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> dimindex(:M) <= dimindex(:N)`;;

let LINEAR_SURJECTIVE_DIMINDEX_LE = `!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> dimindex(:N) <= dimindex(:M)`;;

let LINEAR_BIJECTIVE_DIMINDEX_EQ = `!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> dimindex(:M) = dimindex(:N)`;;

let INVERTIBLE_IMP_SQUARE_MATRIX = `!A:real^N^M. invertible A ==> dimindex(:M) = dimindex(:N)`;;

(* ------------------------------------------------------------------------- *)
(* Considering an n-element vector as an n-by-1 or 1-by-n matrix.            *)
(* ------------------------------------------------------------------------- *)

let rowvector = new_definition
 `(rowvector:real^N->real^N^1) v = lambda i j. v$j`;;

let columnvector = new_definition
 `(columnvector:real^N->real^1^N) v = lambda i j. v$i`;;

let TRANSP_COLUMNVECTOR = `!v. transp(columnvector v) = rowvector v`;;

let TRANSP_ROWVECTOR = `!v. transp(rowvector v) = columnvector v`;;

let DOT_ROWVECTOR_COLUMNVECTOR = `!A:real^N^M v:real^N. columnvector(A ** v) = A ** columnvector v`;;

let DOT_MATRIX_PRODUCT = `!x y:real^N. x dot y = (rowvector x ** columnvector y)$1$1`;;

let DOT_MATRIX_VECTOR_MUL = `!A:real^N^N B:real^N^N x:real^N y:real^N.
      (A ** x) dot (B ** y) =
      ((rowvector x) ** (transp(A) ** B) ** (columnvector y))$1$1`;;

(* ------------------------------------------------------------------------- *)
(* Rank of a matrix. Equivalence of row and column rank is taken from        *)
(* George Mackiw's paper, Mathematics Magazine 1995, p. 285.                 *)
(* ------------------------------------------------------------------------- *)

let MATRIX_VECTOR_MUL_IN_COLUMNSPACE = `!A:real^M^N x:real^M. (A ** x) IN span(columns A)`;;

let SUBSPACE_ORTHOGONAL_TO_VECTOR = `!x. subspace {y | orthogonal x y}`;;

let SUBSPACE_ORTHOGONAL_TO_VECTORS = `!s. subspace {y | (!x. x IN s ==> orthogonal x y)}`;;

let ORTHOGONAL_TO_SPAN = `!s x. (!y. y IN s ==> orthogonal x y)
         ==> !y. y IN span(s) ==> orthogonal x y`;;

let ORTHOGONAL_TO_SPAN_EQ = `!s x. (!y. y IN span(s) ==> orthogonal x y) <=>
         (!y. y IN s ==> orthogonal x y)`;;

let ORTHOGONAL_TO_SPANS_EQ = `!s t. (!x y. x IN span(s) /\ y IN span(t) ==> orthogonal x y) <=>
         (!x y. x IN s /\ y IN t ==> orthogonal x y)`;;

let ORTHOGONAL_NULLSPACE_ROWSPACE = `!A:real^M^N x y:real^M.
        A ** x = vec 0 /\ y IN span(rows A) ==> orthogonal x y`;;

let NULLSPACE_INTER_ROWSPACE = `!A:real^M^N x:real^M. A ** x = vec 0 /\ x IN span(rows A) <=> x = vec 0`;;

let MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE = `!A:real^M^N x y:real^M.
        x IN span(rows A) /\ y IN span(rows A) /\ A ** x = A ** y ==> x = y`;;

let DIM_ROWS_LE_DIM_COLUMNS = `!A:real^M^N. dim(rows A) <= dim(columns A)`;;

let rank = new_definition
 `rank(A:real^M^N) = dim(columns A)`;;

let RANK_ROW = `!A:real^M^N. rank(A) = dim(rows A)`;;

let RANK_TRANSP = `!A:real^M^N. rank(transp A) = rank A`;;

let MATRIX_VECTOR_MUL_BASIS = `!A:real^M^N k. 1 <= k /\ k <= dimindex(:M)
                 ==> A ** (basis k) = column k A`;;

let COLUMNS_IMAGE_BASIS = `!A:real^M^N.
     columns A = IMAGE (\x. A ** x) {basis i | 1 <= i /\ i <= dimindex(:M)}`;;

let RANK_DIM_IM = `!A:real^M^N. rank A = dim(IMAGE (\x. A ** x) (:real^M))`;;

let RANK_BOUND = `!A:real^M^N. rank(A) <= MIN (dimindex(:M)) (dimindex(:N))`;;

let FULL_RANK_INJECTIVE = `!A:real^M^N.
        rank A = dimindex(:M) <=>
        (!x y:real^M. A ** x = A ** y ==> x = y)`;;

let FULL_RANK_SURJECTIVE = `!A:real^M^N.
        rank A = dimindex(:N) <=> (!y:real^N. ?x:real^M. A ** x = y)`;;

let RANK_I = `rank(mat 1:real^N^N) = dimindex(:N)`;;

let MATRIX_FULL_LINEAR_EQUATIONS = `!A:real^M^N b:real^N.
        rank A = dimindex(:N) ==> ?x. A ** x = b`;;

let MATRIX_NONFULL_LINEAR_EQUATIONS_EQ = `!A:real^M^N.
        (?x. ~(x = vec 0) /\ A ** x = vec 0) <=> ~(rank A = dimindex(:M))`;;

let MATRIX_NONFULL_LINEAR_EQUATIONS = `!A:real^M^N.
        ~(rank A = dimindex(:M)) ==> ?x. ~(x = vec 0) /\ A ** x = vec 0`;;

let MATRIX_TRIVIAL_LINEAR_EQUATIONS = `!A:real^M^N.
        dimindex(:N) < dimindex(:M)
        ==> ?x. ~(x = vec 0) /\ A ** x = vec 0`;;

let RANK_EQ_0 = `!A:real^M^N. rank A = 0 <=> A = mat 0`;;

let RANK_0 = `rank(mat 0) = 0`;;

let RANK_MUL_LE_RIGHT = `!A:real^N^M B:real^P^N. rank(A ** B) <= rank(B)`;;

let RANK_MUL_LE_LEFT = `!A:real^N^M B:real^P^N. rank(A ** B) <= rank(A)`;;

let SPAN_COLUMNSPACE = `!A:real^M^N. span(columns A) = {y | ?x. A ** x = y}`;;

let MATRIX_AUGMENTED_LINEAR_EQUATIONS = `!A:real^N^M y:real^N.
        (?x. transp A ** x = y) <=>
        rank(pastecart A (rowvector y)) = rank A`;;

(* ------------------------------------------------------------------------- *)
(* Some bounds on components etc. relative to operator norm.                 *)
(* ------------------------------------------------------------------------- *)

let NORM_COLUMN_LE_ONORM = `!A:real^N^M i. norm(column i A) <= onorm(\x. A ** x)`;;

let MATRIX_COMPONENT_LE_ONORM = `!A:real^N^M i j. abs(A$i$j) <= onorm(\x. A ** x)`;;

let COMPONENT_LE_ONORM = `!f:real^M->real^N i j. linear f ==> abs(matrix f$i$j) <= onorm f`;;

let ONORM_LE_MATRIX_COMPONENT_SUM = `!A:real^N^M.
        onorm(\x. A ** x) <=
        sum (1..dimindex(:M))
            (\i. sum(1..dimindex(:N)) (\j. abs(A$i$j)))`;;

let ONORM_LE_MATRIX_COMPONENT = `!A:real^N^M B.
        (!i j. 1 <= i /\ i <= dimindex(:M) /\
               1 <= j /\ j <= dimindex(:N)
               ==> abs(A$i$j) <= B)
        ==> onorm(\x. A ** x) <= &(dimindex(:M)) * &(dimindex(:N)) * B`;;

let MATRIX_RATIONAL_APPROXIMATION = `!A:real^N^M e.
        &0 < e
        ==> ?B. (!i j. 1 <= i /\ i <= dimindex(:M) /\
                       1 <= j /\ j <= dimindex(:N)
                       ==> rational(B$i$j)) /\
                onorm(\x. (A - B) ** x) < e`;;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas about hyperplanes and halfspaces.                            *)
(* ------------------------------------------------------------------------- *)

let HYPERPLANE_EQ_EMPTY = `!a:real^N b. {x | a dot x = b} = {} <=> a = vec 0 /\ ~(b = &0)`;;

let HYPERPLANE_EQ_UNIV = `!a b. {x | a dot x = b} = (:real^N) <=> a = vec 0 /\ b = &0`;;

let HALFSPACE_EQ_EMPTY_LT = `!a:real^N b. {x | a dot x < b} = {} <=> a = vec 0 /\ b <= &0`;;

let HALFSPACE_EQ_EMPTY_GT = `!a:real^N b. {x | a dot x > b} = {} <=> a = vec 0 /\ b >= &0`;;

let HALFSPACE_EQ_EMPTY_LE = `!a:real^N b. {x | a dot x <= b} = {} <=> a = vec 0 /\ b < &0`;;

let HALFSPACE_EQ_EMPTY_GE = `!a:real^N b. {x | a dot x >= b} = {} <=> a = vec 0 /\ b > &0`;;

(* ------------------------------------------------------------------------- *)
(* A non-injective linear function maps into a hyperplane.                   *)
(* ------------------------------------------------------------------------- *)

let ADJOINT_INJECTIVE = `!f:real^M->real^N.
        linear f
        ==> ((!x y. adjoint f x = adjoint f y ==> x = y) <=>
             (!y. ?x. f x = y))`;;

let ADJOINT_SURJECTIVE = `!f:real^M->real^N.
        linear f
        ==> ((!y. ?x. adjoint f x = y) <=> (!x y. f x = f y ==> x = y))`;;

let ADJOINT_INJECTIVE_INJECTIVE = `!f:real^N->real^N.
        linear f
        ==> ((!x y. adjoint f x = adjoint f y ==> x = y) <=>
             (!x y. f x = f y ==> x = y))`;;

let ADJOINT_INJECTIVE_INJECTIVE_0 = `!f:real^N->real^N.
        linear f
        ==> ((!x. adjoint f x = vec 0 ==> x = vec 0) <=>
             (!x. f x = vec 0 ==> x = vec 0))`;;

let TRANSP_INJECTIVE = `!m:real^M^N.
        (!x y:real^N. transp m ** x = transp m ** y ==> x = y) <=>
        IMAGE (\x. m ** x) (:real^M) = (:real^N)`;;

let TRANSP_SURJECTIVE = `!m:real^M^N.
        IMAGE (\x. transp m ** x) (:real^N) = (:real^M) <=>
        (!x y:real^M. m ** x = m ** y ==> x = y)`;;

let LINEAR_SINGULAR_INTO_HYPERPLANE = `!f:real^N->real^N.
        linear f
        ==> (~(!x y. f(x) = f(y) ==> x = y) <=>
             ?a. ~(a = vec 0) /\ !x. a dot f(x) = &0)`;;

let LINEAR_SINGULAR_IMAGE_HYPERPLANE = `!f:real^N->real^N.
        linear f /\ ~(!x y. f(x) = f(y) ==> x = y)
        ==> ?a. ~(a = vec 0) /\ !s. IMAGE f s SUBSET {x | a dot x = &0}`;;

(* ------------------------------------------------------------------------- *)
(* Orthogonal bases, Gram-Schmidt process, and related theorems.             *)
(* ------------------------------------------------------------------------- *)

let SPAN_DELETE_0 = `!s:real^N->bool. span(s DELETE vec 0) = span s`;;

let DIM_BASIS_IMAGE = `!k. dim(IMAGE basis k:real^N->bool) = CARD((1..dimindex(:N)) INTER k)`;;

let SPAN_IMAGE_SCALE = `!c s. (!x. x IN s ==> ~(c x = &0))
         ==> span (IMAGE (\x:real^N. c(x) % x) s) = span s`;;

let DIM_IMAGE_SCALE = `!c s:real^N->bool.
        (!x. x IN s ==> ~(c x = &0)) ==> dim(IMAGE (\x. c x % x) s) = dim s`;;

let PAIRWISE_ORTHOGONAL_INDEPENDENT = `!s:real^N->bool.
        pairwise orthogonal s /\ ~(vec 0 IN s) ==> independent s`;;

let PAIRWISE_ORTHOGONAL_IMP_FINITE = `!s:real^N->bool. pairwise orthogonal s ==> FINITE s`;;

let GRAM_SCHMIDT_STEP = `!s a x.
        pairwise orthogonal s /\ x IN span s
        ==> orthogonal x (a - vsum s (\b:real^N. (b dot a) / (b dot b) % b))`;;

let ORTHOGONAL_EXTENSION = `!s t:real^N->bool.
        pairwise orthogonal s
        ==> ?u. pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)`;;

let ORTHOGONAL_EXTENSION_STRONG = `!s t:real^N->bool.
        pairwise orthogonal s
        ==> ?u. DISJOINT u (vec 0 INSERT s) /\
                pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)`;;

let ORTHONORMAL_EXTENSION = `!s t:real^N->bool.
        pairwise orthogonal s /\ (!x. x IN s ==> norm x = &1)
        ==> ?u. DISJOINT u s /\
                pairwise orthogonal (s UNION u) /\
                (!x. x IN u ==> norm x = &1) /\
                span(s UNION u) = span(s UNION t)`;;

let VECTOR_IN_ORTHOGONAL_SPANNINGSET = `!a. ?s. a IN s /\ pairwise orthogonal s /\ span s = (:real^N)`;;

let VECTOR_IN_ORTHOGONAL_BASIS = `!a. ~(a = vec 0)
       ==> ?s. a IN s /\ ~(vec 0 IN s) /\
               pairwise orthogonal s /\
               independent s /\
               s HAS_SIZE (dimindex(:N)) /\
               span s = (:real^N)`;;

let VECTOR_IN_ORTHONORMAL_BASIS = `!a. norm a = &1
       ==> ?s. a IN s /\
               pairwise orthogonal s /\
               (!x. x IN s ==> norm x = &1) /\
               independent s /\
               s HAS_SIZE (dimindex(:N)) /\
               span s = (:real^N)`;;

let BESSEL_INEQUALITY = `!s x:real^N.
        pairwise orthogonal s /\ (!x. x IN s ==> norm x = &1)
        ==> sum s (\e. (e dot x) pow 2) <= norm(x) pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Analogous theorems for existence of orthonormal basis for a subspace.     *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_SPANNINGSET_SUBSPACE = `!s:real^N->bool.
        subspace s
        ==> ?b. b SUBSET s /\ pairwise orthogonal b /\ span b = s`;;

let ORTHOGONAL_BASIS_SUBSPACE = `!s:real^N->bool.
        subspace s
        ==> ?b. ~(vec 0 IN b) /\
                b SUBSET s /\
                pairwise orthogonal b /\
                independent b /\
                b HAS_SIZE (dim s) /\
                span b = s`;;

let ORTHONORMAL_BASIS_SUBSPACE = `!s:real^N->bool.
        subspace s
        ==> ?b. b SUBSET s /\
                pairwise orthogonal b /\
                (!x. x IN b ==> norm x = &1) /\
                independent b /\
                b HAS_SIZE (dim s) /\
                span b = s`;;

let ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN = `!s t:real^N->bool.
        span s PSUBSET span t
        ==> ?x. ~(x = vec 0) /\ x IN span t /\
                (!y. y IN span s ==> orthogonal x y)`;;

let ORTHOGONAL_TO_SUBSPACE_EXISTS = `!s:real^N->bool. dim s < dimindex(:N)
                    ==> ?x. ~(x = vec 0) /\ !y. y IN s ==> orthogonal x y`;;

let ORTHOGONAL_TO_VECTOR_EXISTS = `!x:real^N. 2 <= dimindex(:N) ==> ?y. ~(y = vec 0) /\ orthogonal x y`;;

let SPAN_NOT_UNIV_ORTHOGONAL = `!s. ~(span s = (:real^N))
         ==> ?a. ~(a = vec 0) /\ !x. x IN span s ==> a dot x = &0`;;

let SPAN_NOT_UNIV_SUBSET_HYPERPLANE = `!s. ~(span s = (:real^N))
       ==> ?a. ~(a = vec 0) /\ span s SUBSET {x | a dot x = &0}`;;

let LOWDIM_SUBSET_HYPERPLANE = `!s. dim s < dimindex(:N)
       ==> ?a:real^N. ~(a = vec 0) /\ span s SUBSET {x | a dot x = &0}`;;

let VECTOR_EQ_DOT_SPAN = `!b x y:real^N.
        (!v. v IN b ==> v dot x = v dot y) /\ x IN span b /\ y IN span b
        ==> x = y`;;

let ORTHONORMAL_BASIS_EXPAND = `!b x:real^N.
        pairwise orthogonal b /\ (!v. v IN b ==> norm v = &1) /\ x IN span b
   ==> vsum b (\v. (v dot x) % v) = x`;;

let ORTHONORMAL_BASIS_EXPAND_DOT = `!b x y:real^N.
        pairwise orthogonal b /\
        (!v. v IN b ==> norm v = &1) /\
        (x IN span b \/ y IN span b)
        ==> sum b (\v. (v dot x) * (v dot y)) = x dot y`;;

let ORTHONORMAL_BASIS_EXPAND_NORM = `!b x:real^N.
        pairwise orthogonal b /\
        (!v. v IN b ==> norm v = &1) /\
        x IN span b
        ==> sum b (\v. (v dot x) pow 2) = norm x pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Independent and orthogonal subspaces.                                     *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_IMP_INDEPENDENT_SUBSPACES = `!s t:real^N->bool.
        (!a b. a IN s /\ b IN t ==> orthogonal a b)
        ==> s INTER t SUBSET {vec 0}`;;

let INDEPENDENT_SUBSPACES_ALT = `!s t:real^N->bool.
        subspace s /\ subspace t
        ==> (s INTER t SUBSET {vec 0} <=> s INTER t = {vec 0})`;;

let INDEPENDENT_SUBSPACES_0 = `!s t:real^N->bool.
        subspace s /\ subspace t
        ==> (s INTER t SUBSET {vec 0} <=>
             !x y. x IN s /\ y IN t /\ x + y = vec 0
                   ==> x = vec 0 /\ y = vec 0)`;;

let INDEPENDENT_SUBSPACES = `!s t:real^N->bool.
        subspace s /\ subspace t
        ==> (s INTER t SUBSET {vec 0} <=>
             !x y x' y'. x IN s /\ x' IN s /\ y IN t /\ y' IN t /\
                         x + y = x' + y'
                         ==> x = x' /\ y = y')`;;

let ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE = `!s t x y x' y':real^N.
        (!a b. a IN s /\ b IN t ==> orthogonal a b) /\
        x IN span s /\ x' IN span s /\ y IN span t /\ y' IN span t /\
        x + y = x' + y'
        ==> x = x' /\ y = y'`;;

let ORTHOGONAL_SUBSPACE_DECOMP_EXISTS = `!s x:real^N. ?y z. y IN span s /\ (!w. w IN span s ==> orthogonal z w) /\
                      x = y + z`;;

let ORTHOGONAL_SUBSPACE_DECOMP = `!s x. ?!(y,z). y IN span s /\
                  z IN {z:real^N | !x. x IN span s ==> orthogonal z x} /\
                  x = y + z`;;

(* ------------------------------------------------------------------------- *)
(* Existence of isometry between subspaces of same dimension.                *)
(* ------------------------------------------------------------------------- *)

let ISOMETRY_SUBSET_SUBSPACE = `!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s <= dim t
        ==> ?f. linear f /\ IMAGE f s SUBSET t /\
                (!x. x IN s ==> norm(f x) = norm(x))`;;

let ISOMETRIES_SUBSPACES = `!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f g. linear f /\ linear g /\
                  IMAGE f s = t /\ IMAGE g t = s /\
                  (!x. x IN s ==> norm(f x) = norm x) /\
                  (!y. y IN t ==> norm(g y) = norm y) /\
                  (!x. x IN s ==> g(f x) = x) /\
                  (!y. y IN t ==> f(g y) = y)`;;

let ISOMETRY_SUBSPACES = `!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f:real^M->real^N. linear f /\ IMAGE f s = t /\
                               (!x. x IN s ==> norm(f x) = norm(x))`;;

let ISOMETRY_UNIV_SUBSPACE = `!s. subspace s /\ dimindex(:M) = dim s
       ==> ?f:real^M->real^N.
                linear f /\ IMAGE f (:real^M) = s /\
                (!x. norm(f x) = norm(x))`;;

let ISOMETRY_UNIV_SUPERSET_SUBSPACE = `!s. subspace s /\ dim s <= dimindex(:M) /\ dimindex(:M) <= dimindex(:N)
       ==> ?f:real^M->real^N.
                linear f /\ s SUBSET (IMAGE f (:real^M)) /\
                (!x. norm(f x) = norm(x))`;;

let ISOMETRY_UNIV_UNIV = `dimindex(:M) <= dimindex(:N)
   ==> ?f:real^M->real^N. linear f /\ (!x. norm(f x) = norm(x))`;;

let SUBSPACE_ISOMORPHISM = `!s t. subspace s /\ subspace t /\ dim(s) = dim(t)
         ==> ?f:real^M->real^N.
                linear f /\ (IMAGE f s = t) /\
                (!x y. x IN s /\ y IN s /\ f x = f y ==> (x = y))`;;

let ISOMORPHISMS_UNIV_UNIV = `dimindex(:M) = dimindex(:N)
   ==> ?f:real^M->real^N g.
            linear f /\ linear g /\
            (!x. norm(f x) = norm x) /\ (!y. norm(g y) = norm y) /\
            (!x. g(f x) = x) /\ (!y. f(g y) = y)`;;

(* ------------------------------------------------------------------------- *)
(* Properties of special hyperplanes.                                        *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_HYPERPLANE = `!a. subspace {x:real^N | a dot x = &0}`;;

let SUBSPACE_SPECIAL_HYPERPLANE = `!k. subspace {x:real^N | x$k = &0}`;;

let SPECIAL_HYPERPLANE_SPAN = `!k. 1 <= k /\ k <= dimindex(:N)
       ==> {x:real^N | x$k = &0} =
           span(IMAGE basis ((1..dimindex(:N)) DELETE k))`;;

let DIM_SPECIAL_HYPERPLANE = `!k. 1 <= k /\ k <= dimindex(:N)
       ==> dim {x:real^N | x$k = &0} = dimindex(:N) - 1`;;

let LOWDIM_EQ_INTER_HYPERPLANE = `!s t:real^N->bool.
        subspace s /\ subspace t /\ t SUBSET s /\ dim t + 1 = dim s
        ==> ?a. ~(a = vec 0) /\ {x | a dot x = &0} INTER s = t`;;

let LOWDIM_EQ_HYPERPLANE = `!s. dim s = dimindex(:N) - 1
       ==> ?a:real^N. ~(a = vec 0) /\ span s = {x | a dot x = &0}`;;

(* ------------------------------------------------------------------------- *)
(* More theorems about dimensions of different subspaces.                    *)
(* ------------------------------------------------------------------------- *)

let DIM_IMAGE_KERNEL_GEN = `!f:real^M->real^N s.
        linear f /\ subspace s
        ==> dim(IMAGE f s) + dim {x | x IN s /\  f x = vec 0} = dim(s)`;;

let DIM_IMAGE_KERNEL = `!f:real^M->real^N.
        linear f
        ==> dim(IMAGE f (:real^M)) + dim {x | f x = vec 0} = dimindex(:M)`;;

let DIM_SUMS_INTER = `!s t:real^N->bool.
    subspace s /\ subspace t
    ==> dim {x + y | x IN s /\ y IN t} + dim(s INTER t) = dim(s) + dim(t)`;;

let DIM_UNION_INTER = `!s t:real^N->bool.
        subspace s /\ subspace t
        ==> dim(s UNION t) + dim(s INTER t) = dim s + dim t`;;

let DIM_KERNEL_COMPOSE = `!f:real^M->real^N g:real^N->real^P.
        linear f /\ linear g
        ==> dim {x | (g o f) x = vec 0} <=
                dim {x | f(x) = vec 0} +
                dim {y | g(y) = vec 0}`;;

let DIM_ORTHOGONAL_SUM = `!s t:real^N->bool.
        (!x y. x IN s /\ y IN t ==> x dot y = &0)
        ==> dim(s UNION t) = dim(s) + dim(t)`;;

let DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS = `!s t:real^N->bool.
        subspace s /\ subspace t /\ s SUBSET t
        ==> dim {y | y IN t /\ !x. x IN s ==> orthogonal x y} + dim s = dim t`;;

let DIM_SPECIAL_SUBSPACE = `!k. dim {x:real^N |
            !i. 1 <= i /\ i <= dimindex(:N) /\ i IN k ==> x$i = &0} =
       CARD((1..dimindex(:N)) DIFF k)`;;

let INDEPENDENT_UNION = `!s t:real^N->bool.
        independent s /\ independent t /\
        (span s) INTER (span t) SUBSET {vec 0}
        ==> independent(s UNION t)`;;

(* ------------------------------------------------------------------------- *)
(* More injective/surjective versus dimension variants.                      *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INJECTIVE_ON_IFF_DIM = `!f:real^M->real^N s.
        linear f /\ subspace s
        ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
             dim(IMAGE f s) = dim s)`;;

let DIM_INJECTIVE_ON_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ subspace s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> dim(IMAGE f s) = dim s`;;

let DIM_EQ_SUBSPACES = `!s t:real^N->bool.
        subspace s /\ subspace t /\ s SUBSET t /\ dim t <= dim s
        ==> s = t`;;

let DIM_EQ_SUBSPACE = `!s t:real^N->bool.
        subspace s /\ subspace t /\ s SUBSET t
        ==> (dim s = dim t <=> s = t)`;;

let LINEAR_SURJECTIVE_ON_IFF_DIM = `!f:real^M->real^N s t.
        linear f /\ subspace s /\ subspace t /\ IMAGE f s SUBSET t
        ==> (IMAGE f s = t <=> dim(IMAGE f s) = dim t)`;;

let LINEAR_INJECTIVE_IMP_SURJECTIVE_ON = `!f:real^M->real^N s t.
        linear f /\ subspace s /\ subspace t /\
        IMAGE f s SUBSET t /\ dim t <= dim s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> IMAGE f s = t`;;

let LINEAR_SURJECTIVE_IFF_INJECTIVE_ON = `!f:real^M->real^N s t.
        linear f /\ subspace s /\ subspace t /\
        IMAGE f s SUBSET t /\ dim s = dim t
        ==> (IMAGE f s = t <=>
             !x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`;;

let LINEAR_INJECTIVE_IFF_DIM = `!f:real^M->real^N.
        linear f
        ==> ((!x y. f x = f y ==> x = y) <=>
             dim(IMAGE f (:real^M)) = dimindex(:M))`;;

let LINEAR_SURJECTIVE_IFF_DIM = `!f:real^M->real^N.
        linear f
        ==> ((!y. ?x. f x = y) <=>
             dim(IMAGE f (:real^M)) = dimindex(:N))`;;

let LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN = `!f:real^M->real^N.
      dimindex(:M) = dimindex(:N) /\ linear f
      ==> ((!y. ?x. f x = y) <=> (!x y. f x = f y ==> x = y))`;;

let MATRIX_INVERTIBLE_LEFT_GEN = `!f:real^M->real^N.
        linear f /\ dimindex(:N) <= dimindex(:M)
        ==> (invertible(matrix f) <=> ?g. linear g /\ g o f = I)`;;

let MATRIX_INVERTIBLE_LEFT = `!f:real^N->real^N.
        linear f
        ==> (invertible(matrix f) <=> ?g. linear g /\ g o f = I)`;;

let MATRIX_INVERTIBLE_RIGHT_GEN = `!f:real^M->real^N.
        linear f /\ dimindex(:M) <= dimindex(:N)
        ==> (invertible(matrix f) <=> ?g. linear g /\ f o g = I)`;;

let MATRIX_INVERTIBLE_RIGHT = `!f:real^N->real^N.
        linear f
        ==> (invertible(matrix f) <=> ?g. linear g /\ f o g = I)`;;

(* ------------------------------------------------------------------------- *)
(* More about product spaces.                                                *)
(* ------------------------------------------------------------------------- *)

let PASTECART_AS_ORTHOGONAL_SUM = `!x:real^M y:real^N.
        pastecart x y = pastecart x (vec 0) + pastecart (vec 0) y`;;

let PCROSS_AS_ORTHOGONAL_SUM = `!s:real^M->bool t:real^N->bool.
        s PCROSS t =
        {u + v | u IN IMAGE (\x. pastecart x (vec 0)) s /\
                 v IN IMAGE (\y. pastecart (vec 0) y) t}`;;

let DIM_PCROSS = `!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t ==> dim(s PCROSS t) = dim s + dim t`;;

let SPAN_PCROSS_SUBSET = `!s:real^M->bool t:real^N->bool.
        span(s PCROSS t) SUBSET (span s) PCROSS (span t)`;;

let SPAN_PCROSS = `!s:real^M->bool t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ (vec 0 IN s \/ vec 0 IN t)
        ==> span(s PCROSS t) = (span s) PCROSS (span t)`;;

let DIM_PCROSS_STRONG = `!s:real^M->bool t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ (vec 0 IN s \/ vec 0 IN t)
        ==> dim(s PCROSS t) = dim s + dim t`;;

let SPAN_SUMS = `!s t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ vec 0 IN (s UNION t)
        ==> span {x + y | x IN s /\ y IN t} =
            {x + y | x IN span s /\ y IN span t}`;;

(* ------------------------------------------------------------------------- *)
(* More about rank from the rank/nullspace formula.                          *)
(* ------------------------------------------------------------------------- *)

let RANK_NULLSPACE = `!A:real^M^N. rank A + dim {x | A ** x = vec 0} = dimindex(:M)`;;

let RANK_SYLVESTER = `!A:real^N^M B:real^P^N.
        rank(A) + rank(B) <= rank(A ** B) + dimindex(:N)`;;

let RANK_GRAM = `!A:real^M^N. rank(transp A ** A) = rank A`;;

let RANK_TRIANGLE = `!A B:real^M^N. rank(A + B) <= rank(A) + rank(B)`;;

let COVARIANCE_MATRIX_EQ_0 = `!A:real^N^M. transp A ** A = mat 0 <=> A = mat 0`;;

let MATRIX_MUL_COVARIANCE_LCANCEL = `!A:real^N^P B C:real^M^N.
        (transp A ** A) ** B = (transp A ** A) ** C <=> A ** B = A ** C`;;

let MATRIX_MUL_COVARIANCE_RCANCEL = `!A:real^P^N B C:real^N^M.
        B ** (A ** transp A) = C ** (A ** transp A) <=> B ** A = C ** A`;;

let MATRIX_VECTOR_MUL_COVARIANCE_EQ_0 = `!A:real^M^N x. (transp A ** A) ** x = vec 0 <=> A ** x = vec 0`;;

(* ------------------------------------------------------------------------- *)
(* Inverse matrices. These are actually, in general, Moore-Penrose           *)
(* pseudoinverses, but collapse to the usual inverse in the invertible case. *)
(* The extra generality gives some cleaner theorems (e.g. MATRIX_INV_INV)    *)
(* and might have some other applications one day.                           *)
(* ------------------------------------------------------------------------- *)

let matrix_inv = new_definition
 `matrix_inv (A:real^M^N) =
    matrix(\y. @x. (!w. A ** w = vec 0 ==> orthogonal x w) /\
                   (!z. orthogonal (y - A ** x) (A ** z)))`;;

let MOORE_PENROSE_PSEUDOINVERSE,MOORE_PENROSE_PSEUDOINVERSE_UNIQUE =
  let lemma_existence = `!f:real^M->real^N y.
          linear f
          ==> ?x. (!w. f w = vec 0 ==> orthogonal x w) /\
                  (!z. orthogonal (y - f x) (f z))`;;

let SYMMETRIC_MATRIX_INV_RMUL = `!A:real^M^N. symmetric_matrix(A ** matrix_inv A)`;;

let MATRIX_INV_INV = `!A:real^M^N. matrix_inv (matrix_inv A) = A`;;

let MATRIX_INV_EQ = `!A B:real^M^N. matrix_inv A = matrix_inv B <=> A = B`;;

let MATRIX_INV_MUL_OUTER = `!A:real^M^N. matrix_inv A ** A ** matrix_inv A = matrix_inv A`;;

let SYMMETRIC_MATRIX_INV_LMUL = `!A:real^M^N. symmetric_matrix(matrix_inv A ** A)`;;

let MATRIX_INV_UNIQUE_STRONG = `!A:real^M^N X.
        A ** X ** A = A /\ X ** A ** X = X /\
        symmetric_matrix(A ** X) /\ symmetric_matrix(X ** A)
        ==> matrix_inv A = X`;;

let MATRIX_INV_TRANSP = `!A:real^M^N. matrix_inv (transp A) = transp(matrix_inv A)`;;

let TRANSP_MATRIX_INV = `!A:real^M^N. transp(matrix_inv A) = matrix_inv(transp A)`;;

let SYMMETRIC_MATRIX_INV = `!A:real^N^N. symmetric_matrix(matrix_inv A) <=> symmetric_matrix A`;;

let MATRIX_INV_0 = `matrix_inv(mat 0:real^M^N) = mat 0`;;

let MATRIX_INV_EQ_0 = `!A:real^M^N. matrix_inv A = mat 0 <=> A = mat 0`;;

let MATRIX_INV_CMUL = `!c A:real^M^N. matrix_inv (c %% A) = inv(c) %% matrix_inv A`;;

let MATRIX_INV = `!A:real^N^M.
    invertible A ==> A ** matrix_inv A = mat 1 /\ matrix_inv A ** A = mat 1`;;

let MATRIX_INV_LEFT = `!A:real^N^N. matrix_inv A ** A = mat 1 <=> invertible A`;;

let MATRIX_INV_RIGHT = `!A:real^N^N. A ** matrix_inv A = mat 1 <=> invertible A`;;

let MATRIX_MUL_LCANCEL = `!A:real^M^N B:real^P^M C.
        invertible A ==> (A ** B = A ** C <=> B = C)`;;

let MATRIX_MUL_RCANCEL = `!A B:real^M^N C:real^P^M.
        invertible C ==> (A ** C = B ** C <=> A = B)`;;

let RANK_INVERTIBLE_RMUL = `!A:real^M^N B:real^P^M. invertible B ==> rank(A ** B) = rank A`;;

let RANK_INVERTIBLE_LMUL = `!A:real^M^N B:real^P^M. invertible A ==> rank(A ** B) = rank B`;;

let RANK_CMUL = `!A:real^N^M c. rank(c %% A) = if c = &0 then 0 else rank A`;;

let RANK_NEG = `!A:real^N^M. rank(--A) = rank A`;;

let MATRIX_INV_UNIQUE = `!A:real^N^M B. A ** B = mat 1 /\ B ** A = mat 1 ==> matrix_inv A = B`;;

let MATRIX_INV_I = `matrix_inv(mat 1:real^N^N) = mat 1`;;

let INVERTIBLE_MATRIX_INV = `!A:real^M^N. invertible(matrix_inv A) <=> invertible A`;;

let MATRIX_INV_UNIQUE_LEFT = `!A:real^N^N B. A ** B = mat 1 ==> matrix_inv B = A`;;

let MATRIX_INV_UNIQUE_RIGHT = `!A:real^N^N B. A ** B = mat 1 ==> matrix_inv A = B`;;

let MATRIX_INV_COVARIANCE = `!A:real^M^N.
     matrix_inv(transp A ** A) = matrix_inv(A) ** transp(matrix_inv A)`;;

let COVARIANCE_MATRIX_INV = `!A:real^M^N.
        transp(matrix_inv A) ** matrix_inv A = matrix_inv(A ** transp A)`;;

let NORMAL_MATRIX_INV = `!A:real^N^N. normal_matrix(matrix_inv A) <=> normal_matrix A`;;

let MATRIX_INV_COVARIANCE_RMUL = `!A:real^M^N. matrix_inv(transp A ** A) ** transp A = matrix_inv A`;;

let MATRIX_INV_COVARIANCE_LMUL = `!A:real^M^N. transp(A) ** matrix_inv(A ** transp A) = matrix_inv A`;;

let RANK_SIMILAR = `!A:real^N^N U:real^M^N.
        invertible U ==> rank(matrix_inv U ** A ** U) = rank A`;;

let RANK_MATRIX_INV = `!A:real^M^N. rank(matrix_inv A) = rank A`;;

let RANK_MATRIX_INV_RMUL = `!A:real^M^N. rank(A ** matrix_inv A) = rank A`;;

let RANK_MATRIX_INV_LMUL = `!A:real^M^N. rank(matrix_inv A ** A) = rank A`;;

let MATRIX_INV_MULTIPLE_TRANP_RIGHT = `!A:real^M^N.
       matrix_inv A = matrix_inv A ** transp(matrix_inv A) ** transp A`;;

let MATRIX_TRANSP_MULTIPLE_INV_RIGHT = `!A:real^M^N. transp A = transp A ** A ** matrix_inv A`;;

let MATRIX_INV_MULTIPLE_TRANP_LEFT = `!A:real^M^N.
       matrix_inv A = transp A ** transp(matrix_inv A) ** matrix_inv A`;;

let MATRIX_TRANSP_MULTIPLE_INV_LEFT = `!A:real^M^N. transp A = matrix_inv A ** A ** transp A`;;

let MATRIX_VECTOR_MUL_INV_EQ_0 = `!A:real^M^N. matrix_inv A ** x = vec 0 <=> transp A ** x = vec 0`;;

let KERNEL_MATRIX_INV = `!A:real^M^N.
        {x | matrix_inv A ** x = vec 0} = {x | transp A ** x = vec 0}`;;

let IMAGE_MATRIX_INV = `!A:real^M^N.
        IMAGE (\x:real^N. matrix_inv A ** x) UNIV =
        IMAGE (\x. transp A ** x) UNIV`;;

let COMMUTING_MATRIX_INV_COVARIANCE = `!A:real^M^N.
        matrix_inv(transp A ** A) ** (transp A ** A) =
        (transp A ** A) ** matrix_inv(transp A ** A)`;;

let COMMUTING_MATRIX_INV_NORMAL = `!A:real^N^N.
      normal_matrix A ==> matrix_inv A ** A = A ** matrix_inv A`;;

let MATRIX_MUL_INV_EQ_0 = `!A:real^P^N B:real^N^M.
        matrix_inv A ** matrix_inv B = mat 0 <=> B ** A = mat 0`;;

let MATRIX_INV_IDEMPOTENT = `!A:real^N^N. symmetric_matrix A /\ A ** A = A ==> matrix_inv A = A`;;

let IDEMPOTENT_MATRIX_MUL_LINV = `!A:real^N^M.
        (matrix_inv A ** A) ** (matrix_inv A ** A) = matrix_inv A ** A`;;

let IDEMPOTENT_MATRIX_MUL_RINV = `!A:real^N^M.
        (A ** matrix_inv A) ** (A ** matrix_inv A) = A ** matrix_inv A`;;

let MATRIX_INV_MUL_LINV = `!A:real^N^M. matrix_inv(matrix_inv A ** A) = matrix_inv A ** A`;;

let MATRIX_INV_MUL_RINV = `!A:real^N^M. matrix_inv(A ** matrix_inv A) = A ** matrix_inv A`;;

(* ------------------------------------------------------------------------- *)
(* Infinity norm.                                                            *)
(* ------------------------------------------------------------------------- *)

let infnorm = define
 `infnorm (x:real^N) = sup { abs(x$i) | 1 <= i /\ i <= dimindex(:N) }`;;

let NUMSEG_DIMINDEX_NONEMPTY = `?i. i IN 1..dimindex(:N)`;;

let INFNORM_SET_IMAGE = `{abs(x$i) | 1 <= i /\ i <= dimindex(:N)} =
   IMAGE (\i. abs(x$i)) (1..dimindex(:N))`;;

let INFNORM_SET_LEMMA = `FINITE {abs((x:real^N)$i) | 1 <= i /\ i <= dimindex(:N)} /\
   ~({abs(x$i) | 1 <= i /\ i <= dimindex(:N)} = {})`;;

let INFNORM_POS_LE = `!x. &0 <= infnorm x`;;

let INFNORM_TRIANGLE = `!x y. infnorm(x + y) <= infnorm x + infnorm y`;;

let INFNORM_EQ_0 = `!x. infnorm x = &0 <=> x = vec 0`;;

let INFNORM_0 = `infnorm(vec 0) = &0`;;

let INFNORM_NEG = `!x. infnorm(--x) = infnorm x`;;

let INFNORM_SUB = `!x y. infnorm(x - y) = infnorm(y - x)`;;

let REAL_ABS_SUB_INFNORM = `abs(infnorm x - infnorm y) <= infnorm(x - y)`;;

let REAL_ABS_INFNORM = `!x. abs(infnorm x) = infnorm x`;;

let COMPONENT_LE_INFNORM = `!x:real^N i. 1 <= i /\ i <= dimindex (:N) ==> abs(x$i) <= infnorm x`;;

let INFNORM_MUL_LEMMA = `!a x. infnorm(a % x) <= abs a * infnorm x`;;

let INFNORM_MUL = `!a x:real^N. infnorm(a % x) = abs a * infnorm x`;;

let INFNORM_POS_LT = `!x. &0 < infnorm x <=> ~(x = vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* Prove that it differs only up to a bound from Euclidean norm.             *)
(* ------------------------------------------------------------------------- *)

let INFNORM_LE_NORM = `!x. infnorm(x) <= norm(x)`;;

let NORM_LE_INFNORM = `!x:real^N. norm(x) <= sqrt(&(dimindex(:N))) * infnorm(x)`;;

(* ------------------------------------------------------------------------- *)
(* Equality in Cauchy-Schwarz and triangle inequalities.                     *)
(* ------------------------------------------------------------------------- *)

let NORM_CAUCHY_SCHWARZ_EQ = `!x:real^N y. x dot y = norm(x) * norm(y) <=> norm(x) % y = norm(y) % x`;;

let NORM_CAUCHY_SCHWARZ_ABS_EQ = `!x:real^N y. abs(x dot y) = norm(x) * norm(y) <=>
                norm(x) % y = norm(y) % x \/ norm(x) % y = --norm(y) % x`;;

let NORM_TRIANGLE_EQ = `!x y:real^N. norm(x + y) = norm(x) + norm(y) <=> norm(x) % y = norm(y) % x`;;

let DIST_TRIANGLE_EQ = `!x y z. dist(x,z) = dist(x,y) + dist(y,z) <=>
                norm (x - y) % (y - z) = norm (y - z) % (x - y)`;;

let NORM_CROSS_MULTIPLY = `!a b x y:real^N.
        a % x = b % y /\ &0 < a /\ &0 < b
        ==> norm y % x = norm x % y`;;

(* ------------------------------------------------------------------------- *)
(* Collinearity.                                                             *)
(* ------------------------------------------------------------------------- *)

let collinear = new_definition
 `collinear s <=> ?u. !x y. x IN s /\ y IN s ==> ?c. x - y = c % u`;;

let COLLINEAR_ALT2 = `!s:real^N->bool. collinear s <=> ?u v. !x. x IN s ==> ?c. x - u = c % v`;;

let COLLINEAR_ALT = `!s:real^N->bool. collinear s <=> ?u v. !x. x IN s ==> ?c. x = u + c % v`;;

let COLLINEAR_SUBSET = `!s t. collinear t /\ s SUBSET t ==> collinear s`;;

let COLLINEAR_EMPTY = `collinear {}`;;

let COLLINEAR_SING = `!x. collinear {x}`;;

let COLLINEAR_2 = `!x y:real^N. collinear {x,y}`;;

let COLLINEAR_SMALL = `!s. FINITE s /\ CARD s <= 2 ==> collinear s`;;

let COLLINEAR_3 = `!x y z. collinear {x,y,z} <=> collinear {vec 0,x - y,z - y}`;;

let COLLINEAR_LEMMA = `!x y:real^N. collinear {vec 0,x,y} <=>
                   x = vec 0 \/ y = vec 0 \/ ?c. y = c % x`;;

let COLLINEAR_LEMMA_ALT = `!x y. collinear {vec 0,x,y} <=> x = vec 0 \/ ?c. y = c % x`;;

let COLLINEAR_SPAN = `!a b:real^N. collinear{vec 0,a,b} <=> a = vec 0 \/ b IN span {a}`;;

let NORM_CAUCHY_SCHWARZ_EQUAL = `!x y:real^N. abs(x dot y) = norm(x) * norm(y) <=> collinear {vec 0,x,y}`;;

let DOT_CAUCHY_SCHWARZ_EQUAL = `!x y:real^N.
        (x dot y) pow 2 = (x dot x) * (y dot y) <=>
        collinear {vec 0,x,y}`;;

let COLLINEAR_3_EXPAND = `!a b c:real^N. collinear{a,b,c} <=> a = c \/ ?u. b = u % a + (&1 - u) % c`;;

let COLLINEAR_TRIPLES = `!s a b:real^N.
        ~(a = b)
        ==> (collinear(a INSERT b INSERT s) <=>
             !x. x IN s ==> collinear{a,b,x})`;;

let COLLINEAR_4_3 = `!a b c d:real^N.
        ~(a = b)
        ==> (collinear {a,b,c,d} <=> collinear{a,b,c} /\ collinear{a,b,d})`;;

let COLLINEAR_3_TRANS = `!a b c d:real^N.
        collinear{a,b,c} /\ collinear{b,c,d} /\ ~(b = c) ==> collinear{a,b,d}`;;

let ORTHOGONAL_TO_ORTHOGONAL_2D = `!x y z:real^2.
     ~(x = vec 0) /\ orthogonal x y /\ orthogonal x z
     ==> collinear {vec 0,y,z}`;;

let COLLINEAR_3_2D = `!x y z:real^2. collinear{x,y,z} <=>
                  (z$1 - x$1) * (y$2 - x$2) = (y$1 - x$1) * (z$2 - x$2)`;;

let COLLINEAR_3_DOT_MULTIPLES = `!a b c:real^N.
        collinear {a,b,c} <=>
        ((b - a) dot (b - a)) % (c - a) = ((c - a) dot (b - a)) % (b - a)`;;

let ORTHOGONAL_AND_COLLINEAR = `!x y:real^N.
        orthogonal x y /\ collinear{vec 0,x,y} <=> x = vec 0 \/ y = vec 0`;;

(* ------------------------------------------------------------------------- *)
(* Between-ness.                                                             *)
(* ------------------------------------------------------------------------- *)

let between = new_definition
 `between x (a,b) <=> dist(a,b) = dist(a,x) + dist(x,b)`;;

let BETWEEN_REFL = `!a b. between a (a,b) /\ between b (a,b) /\ between a (a,a)`;;

let BETWEEN_REFL_EQ = `!a x. between x (a,a) <=> x = a`;;

let BETWEEN_SYM = `!a b x. between x (a,b) <=> between x (b,a)`;;

let BETWEEN_ANTISYM = `!a b c. between a (b,c) /\ between b (a,c) ==> a = b`;;

let BETWEEN_TRANS = `!a b c d. between a (b,c) /\ between d (a,c) ==> between d (b,c)`;;

let BETWEEN_TRANS_2 = `!a b c d. between a (b,c) /\ between d (a,b) ==> between a (c,d)`;;

let BETWEEN_TRANSLATION = `!a x y. between (a + x) (a + y,a + z) <=> between x (y,z)`;;

let BETWEEN_NORM = `!a b x:real^N.
     between x (a,b) <=> norm(x - a) % (b - x) = norm(b - x) % (x - a)`;;

let BETWEEN_DOT = `!a b x:real^N.
     between x (a,b) <=> (x - a) dot (b - x) = norm(x - a) * norm(b - x)`;;

let BETWEEN_EXISTS_EXTENSION = `!a b x:real^N.
        between b (a,x) /\ ~(b = a) ==> ?d. &0 <= d /\ x = b + d % (b - a)`;;

let BETWEEN_IMP_COLLINEAR = `!a b x:real^N. between x (a,b) ==> collinear {a,x,b}`;;

let BETWEEN_CMUL_LIFT = `!a b c v:real^N.
        between (c % v) (a % v,b % v) <=>
        v = vec 0 \/ between (lift c) (lift a,lift b)`;;

let BETWEEN_1 = `!a b x. between x (a,b) <=>
           drop a <= drop x /\ drop x <= drop b \/
           drop b <= drop x /\ drop x <= drop a`;;

let COLLINEAR_BETWEEN_CASES = `!a b c:real^N.
        collinear {a,b,c} <=>
        between a (b,c) \/ between b (c,a) \/ between c (a,b)`;;

let COLLINEAR_BETWEEN_CASES_2 = `!a b c d:real^N.
        between c (a,b) /\ between d (a,b)
        ==> between d (a,c) \/ between d (c,b)`;;

let BETWEEN_RESTRICTED_CASES = `!a b c x:real^N.
        between x (a,b) /\ between x (a,c) /\ ~(x = a)
        ==> between b (a,c) \/ between c (a,b)`;;

let COLLINEAR_DIST_BETWEEN = `!a b x. collinear {x,a,b} /\
           dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)
           ==> between x (a,b)`;;

let BETWEEN_COLLINEAR_DIST_EQ = `!a b x:real^N.
        between x (a,b) <=>
        collinear {a, x, b} /\
        dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)`;;

let COLLINEAR_1 = `!s:real^1->bool. collinear s`;;

(* ------------------------------------------------------------------------- *)
(* Midpoint between two points.                                              *)
(* ------------------------------------------------------------------------- *)

let midpoint = new_definition
 `midpoint(a,b) = inv(&2) % (a + b)`;;

let MIDPOINT_REFL = `!x. midpoint(x,x) = x`;;

let MIDPOINT_SYM = `!a b. midpoint(a,b) = midpoint(b,a)`;;

let DIST_MIDPOINT = `!a b. dist(a,midpoint(a,b)) = dist(a,b) / &2 /\
         dist(b,midpoint(a,b)) = dist(a,b) / &2 /\
         dist(midpoint(a,b),a) = dist(a,b) / &2 /\
         dist(midpoint(a,b),b) = dist(a,b) / &2`;;

let MIDPOINT_EQ_ENDPOINT = `!a b. (midpoint(a,b) = a <=> a = b) /\
         (midpoint(a,b) = b <=> a = b) /\
         (a = midpoint(a,b) <=> a = b) /\
         (b = midpoint(a,b) <=> a = b)`;;

let BETWEEN_MIDPOINT = `!a b. between (midpoint(a,b)) (a,b) /\ between (midpoint(a,b)) (b,a)`;;

let MIDPOINT_LINEAR_IMAGE = `!f a b. linear f ==> midpoint(f a,f b) = f(midpoint(a,b))`;;

let COLLINEAR_MIDPOINT = `!a b. collinear{a,midpoint(a,b),b}`;;

let MIDPOINT_COLLINEAR = `!a b c:real^N.
        ~(a = c)
        ==> (b = midpoint(a,c) <=> collinear{a,b,c} /\ dist(a,b) = dist(b,c))`;;

let MIDPOINT_BETWEEN = `!a b c:real^N.
        b = midpoint (a,c) <=> between b (a,c) /\ dist (a,b) = dist (b,c)`;;

let DROP_MIDPOINT = `!x y. drop(midpoint(x,y)) = (drop x + drop y) / &2`;;

(* ------------------------------------------------------------------------- *)
(* Intervals, overloaded for standard-ish notation [a,b] and (a,b)           *)
(* ------------------------------------------------------------------------- *)

let open_interval = new_definition
  `open_interval(a:real^N,b:real^N) =
        {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                        ==> a$i < x$i /\ x$i < b$i}`;;

let closed_interval = new_definition
  `closed_interval(l:(real^N#real^N)list) =
         {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                         ==> FST(HD l)$i <= x$i /\ x$i <= SND(HD l)$i}`;;

make_overloadable "interval" `:A`;;

overload_interface("interval",`open_interval`);;
overload_interface("interval",`closed_interval`);;

let interval = `(interval (a,b) = {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                     ==> a$i < x$i /\ x$i < b$i}) /\
   (interval [a,b] = {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                     ==> a$i <= x$i /\ x$i <= b$i})`;;

let IN_INTERVAL = `(!x:real^N.
        x IN interval (a,b) <=>
                !i. 1 <= i /\ i <= dimindex(:N)
                    ==> a$i < x$i /\ x$i < b$i) /\
   (!x:real^N.
        x IN interval [a,b] <=>
                !i. 1 <= i /\ i <= dimindex(:N)
                    ==> a$i <= x$i /\ x$i <= b$i)`;;

let IN_INTERVAL_REFLECT = `(!a b x. (--x) IN interval[--b,--a] <=> x IN interval[a,b]) /\
   (!a b x. (--x) IN interval(--b,--a) <=> x IN interval(a,b))`;;

let REFLECT_INTERVAL = `(!a b:real^N. IMAGE (--) (interval[a,b]) = interval[--b,--a]) /\
   (!a b:real^N. IMAGE (--) (interval(a,b)) = interval(--b,--a))`;;

let INTERVAL_EQ_EMPTY = `((interval [a:real^N,b] = {}) <=>
    ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i < a$i) /\
   ((interval (a:real^N,b) = {}) <=>
    ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i <= a$i)`;;

let INTERVAL_NE_EMPTY = `(~(interval [a:real^N,b] = {}) <=>
    !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i) /\
   (~(interval (a:real^N,b) = {}) <=>
    !i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i)`;;

let SUBSET_INTERVAL_IMP = `((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval[c,d] SUBSET interval[a:real^N,b]) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < c$i /\ d$i < b$i)
    ==> interval[c,d] SUBSET interval(a:real^N,b)) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval(c,d) SUBSET interval[a:real^N,b]) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval(c,d) SUBSET interval(a:real^N,b))`;;

let INTERVAL_SING = `interval[a,a] = {a} /\ interval(a,a) = {}`;;

let SUBSET_INTERVAL = `(interval[c,d] SUBSET interval[a:real^N,b] <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i <= d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)) /\
   (interval[c,d] SUBSET interval(a:real^N,b) <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i <= d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < c$i /\ d$i < b$i)) /\
   (interval(c,d) SUBSET interval[a:real^N,b] <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i < d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)) /\
   (interval(c,d) SUBSET interval(a:real^N,b) <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i < d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i))`;;

let DISJOINT_INTERVAL = `!a b c d:real^N.
        (interval[a,b] INTER interval[c,d] = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i < a$i \/ d$i < c$i \/ b$i < c$i \/ d$i < a$i)) /\
        (interval[a,b] INTER interval(c,d) = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i < a$i \/ d$i <= c$i \/ b$i <= c$i \/ d$i <= a$i)) /\
        (interval(a,b) INTER interval[c,d] = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i <= a$i \/ d$i < c$i \/ b$i <= c$i \/ d$i <= a$i)) /\
        (interval(a,b) INTER interval(c,d) = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i <= a$i \/ d$i <= c$i \/ b$i <= c$i \/ d$i <= a$i))`;;

let ENDS_IN_INTERVAL = `(!a b. a IN interval[a,b] <=> ~(interval[a,b] = {})) /\
   (!a b. b IN interval[a,b] <=> ~(interval[a,b] = {})) /\
   (!a b. ~(a IN interval(a,b))) /\
   (!a b. ~(b IN interval(a,b)))`;;

let ENDS_IN_UNIT_INTERVAL = `vec 0 IN interval[vec 0,vec 1] /\
   vec 1 IN interval[vec 0,vec 1] /\
   ~(vec 0 IN interval(vec 0,vec 1)) /\
   ~(vec 1 IN interval(vec 0,vec 1))`;;

let INTER_INTERVAL = `interval[a,b] INTER interval[c,d] =
        interval[(lambda i. max (a$i) (c$i)),(lambda i. min (b$i) (d$i))]`;;

let INTERVAL_OPEN_SUBSET_CLOSED = `!a b. interval(a,b) SUBSET interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* General "one way" lemma for properties preserved by injective map.        *)
(* ------------------------------------------------------------------------- *)

let WLOG_LINEAR_INJECTIVE_IMAGE_2 = `!P Q. (!f s. P s /\ linear f ==> Q(IMAGE f s)) /\
         (!g t. Q t /\ linear g ==> P(IMAGE g t))
         ==> !f:real^M->real^N.
                linear f /\ (!x y. f x = f y ==> x = y)
                ==> !s. Q(IMAGE f s) <=> P s`;;

let WLOG_LINEAR_INJECTIVE_IMAGE_2_ALT = `!P Q f s. (!h u. P u /\ linear h ==> Q(IMAGE h u)) /\
             (!g t. Q t /\ linear g ==> P(IMAGE g t)) /\
             linear f /\ (!x y. f x = f y ==> x = y)
             ==> (Q(IMAGE f s) <=> P s)`;;

let WLOG_LINEAR_INJECTIVE_IMAGE = `!P. (!f s. P s /\ linear f ==> P(IMAGE f s))
       ==> !f:real^N->real^N. linear f /\ (!x y. f x = f y ==> x = y)
                              ==> !s. P(IMAGE f s) <=> P s`;;

let WLOG_LINEAR_INJECTIVE_IMAGE_ALT = `!P f s. (!g t. P t /\ linear g ==> P(IMAGE g t)) /\
           linear f /\ (!x y. f x = f y ==> x = y)
           ==> (P(IMAGE f s) <=> P s)`;;

(* ------------------------------------------------------------------------- *)
(* Inference rule to apply it conveniently.                                  *)
(*                                                                           *)
(*   |- !f s. P s /\ linear f ==> P(IMAGE f s)  [or /\ commuted]             *)
(* ---------------------------------------------------------------           *)
(*   |- !f s. linear f /\ (!x y. f x = f y ==> x = y)                        *)
(*            ==> (Q(IMAGE f s) <=> P s)                                     *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INVARIANT_RULE th =
  let [f;s] = fst(strip_forall(concl th)) in
  let (rm,rn) = dest_fun_ty (type_of f) in
  let m = last(snd(dest_type rm)) and n = last(snd(dest_type rn)) in
  let th' = INST_TYPE [m,n; n,m] th in
  let th0 = CONJ th th' in
  let th1 = try MATCH_MP WLOG_LINEAR_INJECTIVE_IMAGE_2 th0
            with Failure _ ->
                MATCH_MP WLOG_LINEAR_INJECTIVE_IMAGE_2
            (GEN_REWRITE_RULE (BINOP_CONV o ONCE_DEPTH_CONV) [CONJ_SYM] th0) in
  GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_FORALL_THM] th1;;

(* ------------------------------------------------------------------------- *)
(* Immediate application.                                                    *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (subspace (IMAGE f s) <=> subspace s)`;;

(* ------------------------------------------------------------------------- *)
(* Storage of useful "invariance under linear map / translation" theorems.   *)
(* ------------------------------------------------------------------------- *)

let invariant_under_linear = ref([]:thm list);;

let invariant_under_translation = ref([]:thm list);;

let scaling_theorems = ref([]:thm list);;

(* ------------------------------------------------------------------------- *)
(* Some building-blocks for "union/intersection of" invariance theorems.     *)
(* ------------------------------------------------------------------------- *)

let COUNTABLE_UNION_OF_BIJECTIVE_IMAGE = `!(f:A->B) P P'.
        (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y) /\
        (!s. P' (IMAGE f s) <=> P s)
        ==> (!s. (COUNTABLE UNION_OF P') (IMAGE f s) <=>
                 (COUNTABLE UNION_OF P) s)`;;

let COUNTABLE_INTERSECTION_OF_BIJECTIVE_IMAGE = `!(f:A->B) P P'.
        (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y) /\
        (!s. P' (IMAGE f s) <=> P s)
        ==> (!s. (COUNTABLE INTERSECTION_OF P') (IMAGE f s) <=>
                 (COUNTABLE INTERSECTION_OF P) s)`;;

(* ------------------------------------------------------------------------- *)
(* Scaling theorems and derivation from linear invariance.                   *)
(* ------------------------------------------------------------------------- *)

let AFFINITY_SCALING_TRANSLATION = `!m c:real^N. (\x. m % x + c) = (\x. c + x) o (\x. m % x)`;;

let LINEAR_SCALING = `!c. linear(\x:real^N. c % x)`;;

let INJECTIVE_SCALING = `!c. (!x y:real^N. c % x = c % y ==> x = y) <=> ~(c = &0)`;;

let SURJECTIVE_SCALING = `!c. (!y:real^N. ?x. c % x = y) <=> ~(c = &0)`;;

let SCALING_INVARIANT =
  let pths = (CONJUNCTS o UNDISCH o prove)
   (`&0 < c
     ==> linear(\x:real^N. c % x) /\
         (!x y:real^N. c % x = c % y ==> x = y) /\
         (!y:real^N. ?x. c % x = y)`,
    SIMP_TAC[REAL_LT_IMP_NZ; LINEAR_SCALING;
             INJECTIVE_SCALING; SURJECTIVE_SCALING])
  and sc_tm = `\x:real^N. c % x`
  and sa_tm = `&0:real < c`
  and c_tm = `c:real` in
  fun th ->
    let ith = BETA_RULE(ISPEC sc_tm th) in
    let avs,bod = strip_forall(concl ith) in
    let cjs = conjuncts(lhand bod) in
    let cths = map (fun t -> find(fun th -> aconv (concl th) t) pths) cjs in
    let oth = MP (SPECL avs ith) (end_itlist CONJ cths) in
    GEN c_tm (DISCH sa_tm (GENL avs oth));;

(* ------------------------------------------------------------------------- *)
(* Augmentation of the lists. The "add_linear_invariants" also updates       *)
(* the scaling theorems automatically, so only a few of those will need      *)
(* to be added explicitly.                                                   *)
(* ------------------------------------------------------------------------- *)

let add_scaling_theorems thl =
  (scaling_theorems := (!scaling_theorems) @ thl);;

let add_linear_invariants thl =
  ignore(mapfilter (fun th -> add_scaling_theorems[SCALING_INVARIANT th]) thl);
  (invariant_under_linear := (!invariant_under_linear) @ thl);;

let add_translation_invariants thl =
 (invariant_under_translation := (!invariant_under_translation) @ thl);;

(* ------------------------------------------------------------------------- *)
(* Start with some basic set equivalences.                                   *)
(* We give them all an injectivity hypothesis even if it's not necessary.    *)
(* For just the intersection theorem we add surjectivity (more manageable    *)
(* than assuming that the set isn't empty).                                  *)
(* ------------------------------------------------------------------------- *)

let th_sets = `!f. (!x y. f x = f y ==> x = y)
       ==> (if p then f x else f y) = f(if p then x else y) /\
           (if p then IMAGE f s else IMAGE f t) =
           IMAGE f (if p then s else t) /\
           (f x) INSERT (IMAGE f s) = IMAGE f (x INSERT s) /\
           (IMAGE f s) DELETE (f x) = IMAGE f (s DELETE x) /\
           (IMAGE f s) INTER (IMAGE f t) = IMAGE f (s INTER t) /\
           (IMAGE f s) UNION (IMAGE f t) = IMAGE f (s UNION t) /\
           UNIONS(IMAGE (IMAGE f) u) = IMAGE f (UNIONS u) /\
           (IMAGE f s) DIFF (IMAGE f t) = IMAGE f (s DIFF t) /\
           (IMAGE f s (f x) <=> s x) /\
           ((f x) IN (IMAGE f s) <=> x IN s) /\
           ((f o xs) (n:num) = f(xs n)) /\
           ((f o pt) (tt:real^1) = f(pt tt)) /\
           (IMAGE (f o g) k = IMAGE f (IMAGE g k)) /\
           (DISJOINT (IMAGE f s) (IMAGE f t) <=> DISJOINT s t) /\
           ((IMAGE f s) SUBSET (IMAGE f t) <=> s SUBSET t) /\
           ((IMAGE f s) PSUBSET (IMAGE f t) <=> s PSUBSET t) /\
           (IMAGE f s = IMAGE f t <=> s = t) /\
           ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n) /\
           (FINITE(IMAGE f s) <=> FINITE s) /\
           (INFINITE(IMAGE f s) <=> INFINITE s) /\
           (COUNTABLE(IMAGE f s) <=> COUNTABLE s)`;;

let th_set = `!f:A->B s. (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
              ==> INTERS (IMAGE (IMAGE f) s) = IMAGE f (INTERS s)`;;

let PRESERVES_NORM_PRESERVES_DOT = `!f:real^M->real^N x y.
     linear f /\ (!x. norm(f x) = norm x)
     ==> (f x) dot (f y) = x dot y`;;

let PRESEVES_NORM_PRESERVES_DIST = `!f:real^M->real^N.
        linear f /\ (!x. norm(f x) = norm x)
        ==> !x y. dist(f x,f y) = dist(x,y)`;;

let PRESERVES_NORM_INJECTIVE = `!f:real^M->real^N.
     linear f /\ (!x. norm(f x) = norm x)
     ==> !x y. f x = f y ==> x = y`;;

let ORTHOGONAL_LINEAR_IMAGE_EQ = `!f:real^M->real^N x y.
     linear f /\ (!x. norm(f x) = norm x)
     ==> (orthogonal (f x) (f y) <=> orthogonal x y)`;;

let NORMAL_MATRIX_IFF_SAME_NORM_TRANSP,NORMAL_MATRIX_IFF_SAME_DOT_TRANSP =
    (CONJ_PAIR o prove)
 (`(!A:real^N^N.
         normal_matrix A <=>
         !x. norm(transp A ** x) = norm(A ** x)) /\
   (!A:real^N^N.
         normal_matrix A <=>
         !x y. (transp A ** x) dot (transp A ** y) = (A ** x) dot (A ** y))`,
  REWRITE_TAC[normal_matrix; AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC
   (TAUT `(q <=> r) /\ (p <=> r) ==> (p <=> q) /\ (p <=> r)`) THEN
  CONJ_TAC THENL
   [EQ_TAC THENL [ALL_TAC; SIMP_TAC[NORM_EQ]] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SAME_NORM_SAME_DOT THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN
    GEN_REWRITE_TAC (RAND_CONV o funpow 2 BINDER_CONV o RAND_CONV)
     [GSYM DOT_MATRIX_TRANSP_LMUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN REWRITE_TAC[GSYM DOT_LSUB] THEN
    REWRITE_TAC[FORALL_DOT_EQ_0; MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM MATRIX_EQ_0; GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
    REWRITE_TAC[MATRIX_SUB_EQ] THEN MESON_TAC[]]);;

let NORMAL_MATRIX_KERNEL_TRANSP_EXPLICIT = `!A x:real^N.
        normal_matrix A
        ==> (transp A ** x = vec 0 <=> A ** x = vec 0)`;;

let NORMAL_MATRIX_KERNEL_TRANSP = `!A:real^N^N.
        normal_matrix A
        ==> {x | transp A ** x = vec 0} = {x | A ** x = vec 0}`;;

add_linear_invariants
 [GSYM LINEAR_ADD;
  GSYM LINEAR_CMUL;
  GSYM LINEAR_SUB;
  GSYM LINEAR_NEG;
  MIDPOINT_LINEAR_IMAGE;
  MESON[] `!f:real^M->real^N x.
                (!x. norm(f x) = norm x) ==> norm(f x) = norm x`;
  PRESERVES_NORM_PRESERVES_DOT;
  MESON[dist; LINEAR_SUB]
    `!f:real^M->real^N x y.
        linear f /\ (!x. norm(f x) = norm x)
        ==> dist(f x,f y) = dist(x,y)`;
  MESON[] `!f:real^M->real^N x y.
                (!x y. f x = f y ==> x = y) ==> (f x = f y <=> x = y)`;
  SUBSPACE_LINEAR_IMAGE_EQ;
  ORTHOGONAL_LINEAR_IMAGE_EQ;
  SPAN_LINEAR_IMAGE;
  DEPENDENT_LINEAR_IMAGE_EQ;
  INDEPENDENT_LINEAR_IMAGE_EQ;
  DIM_INJECTIVE_LINEAR_IMAGE];;

add_translation_invariants
 [VECTOR_ARITH `!a x y. a + x:real^N = a + y <=> x = y`;
  NORM_ARITH `!a x y. dist(a + x,a + y) = dist(x,y)`;
  VECTOR_ARITH `!a x y. &1 / &2 % ((a + x) + (a + y)) = a + &1 / &2 % (x + y)`;
  VECTOR_ARITH `!a x y. inv(&2) % ((a + x) + (a + y)) = a + inv(&2) % (x + y)`;
  VECTOR_ARITH `!a x y. (a + x) - (a + y):real^N = x - y`;
  (EQT_ELIM o (REWRITE_CONV[midpoint] THENC(EQT_INTRO o NORM_ARITH)))
               `!a x y. midpoint(a + x,a + y) = a + midpoint(x,y)`;
  (EQT_ELIM o (REWRITE_CONV[between] THENC(EQT_INTRO o NORM_ARITH)))
               `!a x y z. between (a + x) (a + y,a + z) <=> between x (y,z)`];;

let th = `!a s b c:real^N. (a + b) + c IN IMAGE (\x. a + x) s <=> (b + c) IN s`;;

add_translation_invariants [MEM_TRANSLATION];;

let MEM_LINEAR_IMAGE = `!f:real^M->real^N x l.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (MEM (f x) (MAP f l) <=> MEM x l)`;;

add_linear_invariants [MEM_LINEAR_IMAGE];;

let LENGTH_TRANSLATION = `!a:real^N l. LENGTH(MAP (\x. a + x) l) = LENGTH l`;;

let QUANTIFY_SURJECTION_HIGHER_THM = `!f:A->B.
        (!y. ?x. f x = y)
        ==> ((!P. (!x. P x) <=> (!x. P (f x))) /\
             (!P. (?x. P x) <=> (?x. P (f x))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE f s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE f s))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE (IMAGE f) s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE (IMAGE f) s))) /\
             (!P. (!g:real^1->B. P g) <=> (!g. P(f o g))) /\
             (!P. (?g:real^1->B. P g) <=> (?g. P(f o g))) /\
             (!P. (!g:num->B. P g) <=> (!g. P(f o g))) /\
             (!P. (?g:num->B. P g) <=> (?g. P(f o g))) /\
             (!Q. (!l. Q l) <=> (!l. Q(MAP f l))) /\
             (!Q. (?l. Q l) <=> (?l. Q(MAP f l)))) /\
            ((!P. {x | P x} = IMAGE f {x | P(f x)}) /\
             (!Q. {s | Q s} = IMAGE (IMAGE f) {s | Q(IMAGE f s)}) /\
             (!R. {l | R l} = IMAGE (MAP f) {l | R(MAP f l)}))`;;

(* ------------------------------------------------------------------------- *)
(* Apply such quantifier and set expansions once per level at depth.         *)
(* In the PARTIAL version, avoid expanding named variables in list.          *)
(* ------------------------------------------------------------------------- *)

let PARTIAL_EXPAND_QUANTS_CONV avoid th =
  let ath,sth = CONJ_PAIR th in
  let conv1 = GEN_REWRITE_CONV I [ath]
  and conv2 = GEN_REWRITE_CONV I [sth] in
  let conv1' tm =
    let th = conv1 tm in
    if mem (fst(dest_var(fst(dest_abs(rand tm))))) avoid
    then failwith "Not going to expand this variable" else th in
  let rec conv tm =
   ((conv1' THENC BINDER_CONV conv) ORELSEC
    (conv2 THENC
     RAND_CONV(RAND_CONV(ABS_CONV(BINDER_CONV(LAND_CONV conv))))) ORELSEC
    SUB_CONV conv) tm in
  conv;;

let EXPAND_QUANTS_CONV = PARTIAL_EXPAND_QUANTS_CONV [];;
