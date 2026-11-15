(* ======================================================================== *)
(* Properties of power series.                                              *)
(* ======================================================================== *)

needs "Library/analysis.ml";;

(* ------------------------------------------------------------------------ *)
(* More theorems about rearranging finite sums                              *)
(* ------------------------------------------------------------------------ *)

let POWDIFF_LEMMA = `!n x y. sum(0,SUC n)(\p. (x pow p) * y pow ((SUC n) - p)) =
                y * sum(0,SUC n)(\p. (x pow p) * (y pow (n - p)))`;;

let POWDIFF = `!n x y. (x pow (SUC n)) - (y pow (SUC n)) =
                (x - y) * sum(0,SUC n)(\p. (x pow p) * (y pow (n - p)))`;;

let POWREV = `!n x y. sum(0,SUC n)(\p. (x pow p) * (y pow (n - p))) =
                sum(0,SUC n)(\p. (x pow (n - p)) * (y pow p))`;;

(* ------------------------------------------------------------------------ *)
(* Show (essentially) that a power series has a "circle" of convergence,    *)
(* i.e. if it sums for x, then it sums absolutely for z with |z| < |x|.     *)
(* ------------------------------------------------------------------------ *)

let POWSER_INSIDEA = `!f x z. summable (\n. f(n) * (x pow n)) /\ abs(z) < abs(x)
        ==> summable (\n. abs(f(n)) * (z pow n))`;;

(* ------------------------------------------------------------------------ *)
(* Weaker but more commonly useful form for non-absolute convergence        *)
(* ------------------------------------------------------------------------ *)

let POWSER_INSIDE = `!f x z. summable (\n. f(n) * (x pow n)) /\ abs(z) < abs(x)
        ==> summable (\n. f(n) * (z pow n))`;;

(* ------------------------------------------------------------------------ *)
(* Define formal differentiation of power series                            *)
(* ------------------------------------------------------------------------ *)

let diffs = new_definition
  `diffs c = (\n. &(SUC n) * c(SUC n))`;;

(* ------------------------------------------------------------------------ *)
(* Lemma about distributing negation over it                                *)
(* ------------------------------------------------------------------------ *)

let DIFFS_NEG = `!c. diffs(\n. --(c n)) = \n. --((diffs c) n)`;;

(* ------------------------------------------------------------------------ *)
(* Show that we can shift the terms down one                                *)
(* ------------------------------------------------------------------------ *)

let DIFFS_LEMMA = `!n c x. sum(0,n) (\n. (diffs c)(n) * (x pow n)) =
           sum(0,n) (\n. &n * c(n) * (x pow (n - 1))) +
             (&n * c(n) * x pow (n - 1))`;;

let DIFFS_LEMMA2 = `!n c x. sum(0,n) (\n. &n * c(n) * (x pow (n - 1))) =
           sum(0,n) (\n. (diffs c)(n) * (x pow n)) -
                (&n * c(n) * x pow (n - 1))`;;

let DIFFS_EQUIV = `!c x. summable(\n. (diffs c)(n) * (x pow n)) ==>
      (\n. &n * c(n) * (x pow (n - 1))) sums
         (suminf(\n. (diffs c)(n) * (x pow n)))`;;

(* ======================================================================== *)
(* Show term-by-term differentiability of power series                      *)
(* (NB we hypothesize convergence of first two derivatives; we could prove  *)
(*  they all have the same radius of convergence, but we don't need to.)    *)
(* ======================================================================== *)

let TERMDIFF_LEMMA1 = `!m z h.
     sum(0,m)(\p. (((z + h) pow (m - p)) * (z pow p)) - (z pow m)) =
       sum(0,m)(\p. (z pow p) *
       (((z + h) pow (m - p)) - (z pow (m - p))))`;;

let TERMDIFF_LEMMA2 = `!z h. ~(h = &0) ==>
       (((((z + h) pow n) - (z pow n)) / h) - (&n * (z pow (n - 1))) =
        h * sum(0,n - 1)(\p. (z pow p) *
              sum(0,(n - 1) - p)
                (\q. ((z + h) pow q) *
                       (z pow (((n - 2) - p) - q)))))`;;

let TERMDIFF_LEMMA3 = `!z h n K. ~(h = &0) /\ abs(z) <= K /\ abs(z + h) <= K ==>
    abs(((((z + h) pow n) - (z pow n)) / h) - (&n * (z pow (n - 1))))
        <= &n * &(n - 1) * (K pow (n - 2)) * abs(h)`;;

let TERMDIFF_LEMMA4 = `!f K k. &0 < k /\
           (!h. &0 < abs(h) /\ abs(h) < k ==> abs(f h) <= K * abs(h))
        ==> (f tends_real_real &0)(&0)`;;

let TERMDIFF_LEMMA5 = `!f g k. &0 < k /\
         summable(f) /\
         (!h. &0 < abs(h) /\ abs(h) < k ==> !n. abs(g(h) n) <= (f(n) * abs(h)))
             ==> ((\h. suminf(g h)) tends_real_real &0)(&0)`;;

let TERMDIFF = `!c K. summable(\n. c(n) * (K pow n)) /\
         summable(\n. (diffs c)(n) * (K pow n)) /\
         summable(\n. (diffs(diffs c))(n) * (K pow n)) /\
         abs(x) < abs(K)
        ==> ((\x. suminf (\n. c(n) * (x pow n))) diffl
             (suminf (\n. (diffs c)(n) * (x pow n))))(x)`;;

(* ------------------------------------------------------------------------- *)
(* I eventually decided to get rid of the pointless side-conditions.         *)
(* ------------------------------------------------------------------------- *)

let SEQ_NPOW = `!x. abs(x) < &1 ==> (\n. &n * x pow n) tends_num_real &0`;;

let TERMDIFF_CONVERGES = `!K. (!x. abs(x) < K ==> summable(\n. c(n) * x pow n))
       ==> !x. abs(x) < K ==> summable (\n. diffs c n * x pow n)`;;

let TERMDIFF_STRONG = `!c K x.
        summable(\n. c(n) * (K pow n)) /\ abs(x) < abs(K)
        ==> ((\x. suminf (\n. c(n) * (x pow n))) diffl
             (suminf (\n. (diffs c)(n) * (x pow n))))(x)`;;

(* ------------------------------------------------------------------------- *)
(* Term-by-term comparison of power series.                                  *)
(* ------------------------------------------------------------------------- *)

let POWSER_0 = `!a. (\n. a n * (&0) pow n) sums a(0)`;;

let POWSER_LIMIT_0 = `!f a s. &0 < s /\
           (!x. abs(x) < s ==> (\n. a n * x pow n) sums (f x))
           ==> (f tends_real_real a(0))(&0)`;;

let POWSER_LIMIT_0_STRONG = `!f a s.
        &0 < s /\
        (!x. &0 < abs(x) /\ abs(x) < s ==> (\n. a n * x pow n) sums (f x))
        ==> (f tends_real_real a(0))(&0)`;;

let POWSER_EQUAL_0 = `!f a b P.
        (!e. &0 < e ==> ?x. P x /\ &0 < abs x /\ abs(x) < e) /\
        (!x. &0 < abs(x) /\ P x
             ==> (\n. a n * x pow n) sums (f x) /\
                 (\n. b n * x pow n) sums (f x))
        ==> (a(0) = b(0))`;;

let POWSER_EQUAL = `!f a b P.
        (!e. &0 < e ==> ?x. P x /\ &0 < abs x /\ abs(x) < e) /\
        (!x. P x ==> (\n. a n * x pow n) sums (f x) /\
                     (\n. b n * x pow n) sums (f x))
        ==> (a = b)`;;

(* ======================================================================== *)
(* Definitions of the transcendental functions etc.                         *)
(* ======================================================================== *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* To avoid all those beta redexes vanishing without trace...                *)
(* ------------------------------------------------------------------------- *)

set_basic_rewrites (subtract' equals_thm (basic_rewrites())
   [SPEC_ALL BETA_THM]);;

(* ------------------------------------------------------------------------ *)
(* Some miscellaneous lemmas                                                *)
(* ------------------------------------------------------------------------ *)

let MULT_DIV_2 = `!n. (2 * n) DIV 2 = n`;;

let EVEN_DIV2 = `!n. ~(EVEN n) ==> ((SUC n) DIV 2 = SUC((n - 1) DIV 2))`;;

(* ------------------------------------------------------------------------ *)
(* Now set up real numbers interface                                        *)
(* ------------------------------------------------------------------------ *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Another lost lemma.                                                       *)
(* ------------------------------------------------------------------------- *)

let POW_ZERO = `!n x. (x pow n = &0) ==> (x = &0)`;;

let POW_ZERO_EQ = `!n x. (x pow (SUC n) = &0) <=> (x = &0)`;;

let POW_LT = `!n x y. &0 <= x /\ x < y ==> (x pow (SUC n)) < (y pow (SUC n))`;;

let POW_EQ = `!n x y. &0 <= x /\ &0 <= y /\ (x pow (SUC n) = y pow (SUC n))
        ==> (x = y)`;;

(* ------------------------------------------------------------------------- *)
(* Basic differentiation theorems --- none yet.                              *)
(* ------------------------------------------------------------------------- *)

let diff_net = ref empty_net;;

let add_to_diff_net th =
  let t = lhand(rator(rand(concl th))) in
  let net = !diff_net in
  let net' = enter [] (t,PART_MATCH (lhand o rator o rand) th) net in
  diff_net := net';;

(* ------------------------------------------------------------------------ *)
(* The three functions we define by series are exp, sin, cos                *)
(* ------------------------------------------------------------------------ *)

let exp = new_definition
  `exp(x) = suminf(\n. ((\n. inv(&(FACT n)))) n * (x pow n))`;;

let sin = new_definition
  `sin(x) = suminf(\n. ((\n. if EVEN n then &0 else
      ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n))`;;

let cos = new_definition
  `cos(x) = suminf(\n. ((\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n)
       else &0)) n * (x pow n))`;;

(* ------------------------------------------------------------------------ *)
(* Show the series for exp converges, using the ratio test                  *)
(* ------------------------------------------------------------------------ *)

let REAL_EXP_CONVERGES = `!x. (\n. ((\n. inv(&(FACT n)))) n * (x pow n)) sums exp(x)`;;

(* ------------------------------------------------------------------------ *)
(* Show by the comparison test that sin and cos converge                    *)
(* ------------------------------------------------------------------------ *)

let SIN_CONVERGES = `!x. (\n. ((\n. if EVEN n then &0 else
  ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n)) sums
  sin(x)`;;

let COS_CONVERGES = `!x. (\n. ((\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n) else &0)) n
    * (x pow n)) sums cos(x)`;;

(* ------------------------------------------------------------------------ *)
(* Show what the formal derivatives of these series are                     *)
(* ------------------------------------------------------------------------ *)

let REAL_EXP_FDIFF = `diffs (\n. inv(&(FACT n))) = (\n. inv(&(FACT n)))`;;

let SIN_FDIFF = `diffs (\n. if EVEN n then &0 else ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))
   = (\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n) else &0)`;;

let COS_FDIFF = `diffs (\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n) else &0) =
  (\n. --(((\n. if EVEN n then &0 else ((--(&1)) pow ((n - 1) DIV 2)) /
   &(FACT n))) n))`;;

(* ------------------------------------------------------------------------ *)
(* Now at last we can get the derivatives of exp, sin and cos               *)
(* ------------------------------------------------------------------------ *)

let SIN_NEGLEMMA = `!x. --(sin x) = suminf (\n. --(((\n. if EVEN n then &0 else ((--(&1))
        pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n)))`;;

let DIFF_EXP = `!x. (exp diffl exp(x))(x)`;;

let DIFF_SIN = `!x. (sin diffl cos(x))(x)`;;

let DIFF_COS = `!x. (cos diffl --(sin(x)))(x)`;;

(* ------------------------------------------------------------------------- *)
(* Differentiation conversion.                                               *)
(* ------------------------------------------------------------------------- *)

let DIFF_CONV =
  let lookup_expr tm =
    tryfind (fun f -> f tm) (lookup tm (!diff_net)) in
  let v = `x:real` and k = `k:real` and diffl_tm = `(diffl)` in
  let DIFF_var = SPEC v DIFF_X
  and DIFF_const = SPECL [k;v] DIFF_CONST in
  let uneta_CONV = REWR_CONV (GSYM ETA_AX) in
  let rec DIFF_CONV tm =
    if not (is_abs tm) then
      let th0 = uneta_CONV tm in
      let th1 = DIFF_CONV (rand(concl th0)) in
      CONV_RULE (RATOR_CONV(LAND_CONV(K(SYM th0)))) th1 else
    let x,bod = dest_abs tm in
    if bod = x then INST [x,v] DIFF_var
    else if not(free_in x bod) then INST [bod,k; x,v] DIFF_const else
    let th = lookup_expr tm in
    let hyp = fst(dest_imp(concl th)) in
    let hyps = conjuncts hyp in
    let dhyps,sides = partition
      (fun t -> try funpow 3 rator t = diffl_tm
                with Failure _ -> false) hyps in
    let tha = CONJ_ACI_RULE(mk_eq(hyp,list_mk_conj(dhyps@sides))) in
    let thb = CONV_RULE (LAND_CONV (K tha)) th in
    let dths = map (DIFF_CONV o lhand o rator) dhyps in
    MATCH_MP thb (end_itlist CONJ (dths @ map ASSUME sides)) in
  fun tm ->
    let xv = try bndvar tm with Failure _ -> v in
    GEN xv (DISCH_ALL(DIFF_CONV tm));;

(* ------------------------------------------------------------------------- *)
(* Processed versions of composition theorems.                               *)
(* ------------------------------------------------------------------------- *)

let DIFF_COMPOSITE = `((f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl --(l / (f(x) pow 2)))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)) /\
   ((f diffl l)(x) ==> ((\x. --(f x)) diffl --l)(x)) /\
   ((g diffl m)(x) ==>
         ((\x. (g x) pow n) diffl ((&n * (g x) pow (n - 1)) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. exp(g x)) diffl (exp(g x) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. sin(g x)) diffl (cos(g x) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. cos(g x)) diffl (--(sin(g x)) * m))(x))`;;

do_list add_to_diff_net (CONJUNCTS DIFF_COMPOSITE);;

(* ------------------------------------------------------------------------- *)
(* Tactic for goals "(f diffl l) x"                                          *)
(* ------------------------------------------------------------------------- *)

let DIFF_TAC =
  W(fun (asl,w) -> MP_TAC(SPEC(rand w) (DIFF_CONV(lhand(rator w)))) THEN
                   MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC);;

(* ------------------------------------------------------------------------- *)
(* Prove differentiability terms.                                            *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIABLE_RULE =
  let pth = `(f diffl l) x ==> f differentiable x`;;

let DIFFERENTIABLE_CONV = EQT_INTRO o DIFFERENTIABLE_RULE;;

(* ------------------------------------------------------------------------- *)
(* Prove continuity via differentiability (weak but useful).                 *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_RULE =
  let pth = `!f x. f differentiable x ==> f contl x`;;

let CONTINUOUS_CONV = EQT_INTRO o CONTINUOUS_RULE;;

(* ------------------------------------------------------------------------ *)
(* Properties of the exponential function                                   *)
(* ------------------------------------------------------------------------ *)

let REAL_EXP_0 = `exp(&0) = &1`;;

let REAL_EXP_LE_X = `!x. &0 <= x ==> (&1 + x) <= exp(x)`;;

let REAL_EXP_LT_1 = `!x. &0 < x ==> &1 < exp(x)`;;

let REAL_EXP_ADD_MUL = `!x y. exp(x + y) * exp(--x) = exp(y)`;;

let REAL_EXP_NEG_MUL = `!x. exp(x) * exp(--x) = &1`;;

let REAL_EXP_NEG_MUL2 = `!x. exp(--x) * exp(x) = &1`;;

let REAL_EXP_NEG = `!x. exp(--x) = inv(exp(x))`;;

let REAL_EXP_ADD = `!x y. exp(x + y) = exp(x) * exp(y)`;;

let REAL_EXP_POS_LE = `!x. &0 <= exp(x)`;;

let REAL_EXP_NZ = `!x. ~(exp(x) = &0)`;;

let REAL_EXP_POS_LT = `!x. &0 < exp(x)`;;

let REAL_EXP_N = `!n x. exp(&n * x) = exp(x) pow n`;;

let REAL_EXP_SUB = `!x y. exp(x - y) = exp(x) / exp(y)`;;

let REAL_EXP_MONO_IMP = `!x y. x < y ==> exp(x) < exp(y)`;;

let REAL_EXP_MONO_LT = `!x y. exp(x) < exp(y) <=> x < y`;;

let REAL_EXP_MONO_LE = `!x y. exp(x) <= exp(y) <=> x <= y`;;

let REAL_EXP_INJ = `!x y. (exp(x) = exp(y)) <=> (x = y)`;;

let REAL_EXP_TOTAL_LEMMA = `!y. &1 <= y ==> ?x. &0 <= x /\ x <= y - &1 /\ (exp(x) = y)`;;

let REAL_EXP_TOTAL = `!y. &0 < y ==> ?x. exp(x) = y`;;

let REAL_EXP_BOUND_LEMMA = `!x. &0 <= x /\ x <= inv(&2) ==> exp(x) <= &1 + &2 * x`;;

(* ------------------------------------------------------------------------ *)
(* Properties of the logarithmic function                                   *)
(* ------------------------------------------------------------------------ *)

let ln = new_definition
  `ln x = @u. exp(u) = x`;;

let LN_EXP = `!x. ln(exp x) = x`;;

let REAL_EXP_LN = `!x. (exp(ln x) = x) <=> &0 < x`;;

let EXP_LN = `!x. &0 < x ==> exp(ln x) = x`;;

let LN_MUL = `!x y. &0 < x /\ &0 < y ==> (ln(x * y) = ln(x) + ln(y))`;;

let LN_INJ = `!x y. &0 < x /\ &0 < y ==> ((ln(x) = ln(y)) <=> (x = y))`;;

let LN_1 = `ln(&1) = &0`;;

let LN_INV = `!x. &0 < x ==> (ln(inv x) = --(ln x))`;;

let LN_DIV = `!x. &0 < x /\ &0 < y ==> (ln(x / y) = ln(x) - ln(y))`;;

let LN_MONO_LT = `!x y. &0 < x /\ &0 < y ==> (ln(x) < ln(y) <=> x < y)`;;

let LN_MONO_LE = `!x y. &0 < x /\ &0 < y ==> (ln(x) <= ln(y) <=> x <= y)`;;

let LN_POW = `!n x. &0 < x ==> (ln(x pow n) = &n * ln(x))`;;

let LN_LE = `!x. &0 <= x ==> ln(&1 + x) <= x`;;

let LN_LT_X = `!x. &0 < x ==> ln(x) < x`;;

let LN_POS = `!x. &1 <= x ==> &0 <= ln(x)`;;

let LN_POS_LT = `!x. &1 < x ==> &0 < ln(x)`;;

let DIFF_LN = `!x. &0 < x ==> (ln diffl (inv x))(x)`;;

(* ------------------------------------------------------------------------ *)
(* Some properties of roots (easier via logarithms)                         *)
(* ------------------------------------------------------------------------ *)

let root = new_definition
  `root(n) x = @u. (&0 < x ==> &0 < u) /\ (u pow n = x)`;;

let ROOT_LT_LEMMA = `!n x. &0 < x ==> (exp(ln(x) / &(SUC n)) pow (SUC n) = x)`;;

let ROOT_LN = `!x. &0 < x ==> !n. root(SUC n) x = exp(ln(x) / &(SUC n))`;;

let ROOT_0 = `!n. root(SUC n) (&0) = &0`;;

let ROOT_1 = `!n. root(SUC n) (&1) = &1`;;

let ROOT_POW_POS = `!n x. &0 <= x ==> ((root(SUC n) x) pow (SUC n) = x)`;;

let POW_ROOT_POS = `!n x. &0 <= x ==> (root(SUC n)(x pow (SUC n)) = x)`;;

let ROOT_POS_POSITIVE = `!x n. &0 <= x ==> &0 <= root(SUC n) x`;;

let ROOT_POS_UNIQ = `!n x y. &0 <= x /\ &0 <= y /\ (y pow (SUC n) = x)
           ==> (root (SUC n) x = y)`;;

let ROOT_MUL = `!n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x * y) = root(SUC n) x * root(SUC n) y)`;;

let ROOT_INV = `!n x. &0 <= x ==> (root(SUC n) (inv x) = inv(root(SUC n) x))`;;

let ROOT_DIV = `!n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x / y) = root(SUC n) x / root(SUC n) y)`;;

let ROOT_MONO_LT = `!x y. &0 <= x /\ x < y ==> root(SUC n) x < root(SUC n) y`;;

let ROOT_MONO_LE = `!x y. &0 <= x /\ x <= y ==> root(SUC n) x <= root(SUC n) y`;;

let ROOT_MONO_LT_EQ = `!x y. &0 <= x /\ &0 <= y ==> (root(SUC n) x < root(SUC n) y <=> x < y)`;;

let ROOT_MONO_LE_EQ = `!x y. &0 <= x /\ &0 <= y ==> (root(SUC n) x <= root(SUC n) y <=> x <= y)`;;

let ROOT_INJ = `!x y. &0 <= x /\ &0 <= y ==> ((root(SUC n) x = root(SUC n) y) <=> (x = y))`;;

(* ------------------------------------------------------------------------- *)
(* Special case of square roots, a few theorems not already present.         *)
(* ------------------------------------------------------------------------- *)

let SQRT_EVEN_POW2 = `!n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))`;;

let REAL_DIV_SQRT = `!x. &0 <= x ==> x / sqrt(x) = sqrt(x)`;;

(* ------------------------------------------------------------------------- *)
(* Derivative of sqrt (could do the other roots with a bit more care).       *)
(* ------------------------------------------------------------------------- *)

let DIFF_SQRT = `!x. &0 < x ==> (sqrt diffl inv(&2 * sqrt(x))) x`;;

let DIFF_SQRT_COMPOSITE = `!g m x. (g diffl m)(x) /\ &0 < g x
           ==> ((\x. sqrt(g x)) diffl (inv(&2 * sqrt(g x)) * m))(x)`;;

(* ------------------------------------------------------------------------ *)
(* Basic properties of the trig functions                                   *)
(* ------------------------------------------------------------------------ *)

let SIN_0 = `sin(&0) = &0`;;

let COS_0 = `cos(&0) = &1`;;

let SIN_CIRCLE = `!x. (sin(x) pow 2) + (cos(x) pow 2) = &1`;;

let SIN_BOUND = `!x. abs(sin x) <= &1`;;

let SIN_BOUNDS = `!x. --(&1) <= sin(x) /\ sin(x) <= &1`;;

let COS_BOUND = `!x. abs(cos x) <= &1`;;

let COS_BOUNDS = `!x. --(&1) <= cos(x) /\ cos(x) <= &1`;;

let SIN_COS_ADD = `!x y. ((sin(x + y) - ((sin(x) * cos(y)) + (cos(x) * sin(y)))) pow 2) +
         ((cos(x + y) - ((cos(x) * cos(y)) - (sin(x) * sin(y)))) pow 2) = &0`;;

let SIN_COS_NEG = `!x. ((sin(--x) + (sin x)) pow 2) +
       ((cos(--x) - (cos x)) pow 2) = &0`;;

let SIN_ADD = `!x y. sin(x + y) = (sin(x) * cos(y)) + (cos(x) * sin(y))`;;

let COS_ADD = `!x y. cos(x + y) = (cos(x) * cos(y)) - (sin(x) * sin(y))`;;

let SIN_NEG = `!x. sin(--x) = --(sin(x))`;;

let COS_NEG = `!x. cos(--x) = cos(x)`;;

let SIN_DOUBLE = `!x. sin(&2 * x) = &2 * sin(x) * cos(x)`;;

let COS_DOUBLE = `!x. cos(&2 * x) = (cos(x) pow 2) - (sin(x) pow 2)`;;

let COS_ABS = `!x. cos(abs x) = cos(x)`;;

(* ------------------------------------------------------------------------ *)
(* Show that there's a least positive x with cos(x) = 0; hence define pi    *)
(* ------------------------------------------------------------------------ *)

let SIN_PAIRED = `!x. (\n. (((--(&1)) pow n) / &(FACT((2 * n) + 1)))
         * (x pow ((2 * n) + 1))) sums (sin x)`;;

let SIN_POS = `!x. &0 < x /\ x < &2 ==> &0 < sin(x)`;;

let COS_PAIRED = `!x. (\n. (((--(&1)) pow n) / &(FACT(2 * n)))
         * (x pow (2 * n))) sums (cos x)`;;

let COS_2 = `cos(&2) < &0`;;

let COS_ISZERO = `?!x. &0 <= x /\ x <= &2 /\ (cos x = &0)`;;

let pi = new_definition
  `pi = &2 * @x. &0 <= x /\ x <= &2 /\ (cos x = &0)`;;

(* ------------------------------------------------------------------------ *)
(* Periodicity and related properties of the trig functions                 *)
(* ------------------------------------------------------------------------ *)

let PI2 = `pi / &2 = @x. &0 <= x /\ x <= &2 /\ (cos(x) = &0)`;;

let COS_PI2 = `cos(pi / &2) = &0`;;

let PI2_BOUNDS = `&0 < (pi / &2) /\ (pi / &2) < &2`;;

let PI_POS = `&0 < pi`;;

let SIN_PI2 = `sin(pi / &2) = &1`;;

let COS_PI = `cos(pi) = --(&1)`;;

let SIN_PI = `sin(pi) = &0`;;

let SIN_COS = `!x. sin(x) = cos((pi / &2) - x)`;;

let COS_SIN = `!x. cos(x) = sin((pi / &2) - x)`;;

let SIN_PERIODIC_PI = `!x. sin(x + pi) = --(sin(x))`;;

let COS_PERIODIC_PI = `!x. cos(x + pi) = --(cos(x))`;;

let SIN_PERIODIC = `!x. sin(x + (&2 * pi)) = sin(x)`;;

let COS_PERIODIC = `!x. cos(x + (&2 * pi)) = cos(x)`;;

let COS_NPI = `!n. cos(&n * pi) = --(&1) pow n`;;

let SIN_NPI = `!n. sin(&n * pi) = &0`;;

let SIN_POS_PI2 = `!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)`;;

let COS_POS_PI2 = `!x. &0 < x /\ x < pi / &2 ==> &0 < cos(x)`;;

let COS_POS_PI = `!x. --(pi / &2) < x /\ x < pi / &2 ==> &0 < cos(x)`;;

let SIN_POS_PI = `!x. &0 < x /\ x < pi ==> &0 < sin(x)`;;

let SIN_POS_PI_LE = `!x. &0 <= x /\ x <= pi ==> &0 <= sin(x)`;;

let COS_TOTAL = `!y. --(&1) <= y /\ y <= &1 ==> ?!x. &0 <= x /\ x <= pi /\ (cos(x) = y)`;;

let SIN_TOTAL = `!y. --(&1) <= y /\ y <= &1 ==>
        ?!x.  --(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y)`;;

let COS_ZERO_LEMMA = `!x. &0 <= x /\ (cos(x) = &0) ==>
      ?n. ~EVEN n /\ (x = &n * (pi / &2))`;;

let SIN_ZERO_LEMMA = `!x. &0 <= x /\ (sin(x) = &0) ==>
        ?n. EVEN n /\ (x = &n * (pi / &2))`;;

let COS_ZERO = `!x. (cos(x) = &0) <=> (?n. ~EVEN n /\ (x = &n * (pi / &2))) \/
                         (?n. ~EVEN n /\ (x = --(&n * (pi / &2))))`;;

let SIN_ZERO = `!x. (sin(x) = &0) <=> (?n. EVEN n /\ (x = &n * (pi / &2))) \/
                         (?n. EVEN n /\ (x = --(&n * (pi / &2))))`;;

let SIN_ZERO_PI = `!x. (sin(x) = &0) <=> (?n. x = &n * pi) \/ (?n. x = --(&n * pi))`;;

let COS_ONE_2PI = `!x. (cos(x) = &1) <=> (?n. x = &n * &2 * pi) \/ (?n. x = --(&n * &2 * pi))`;;

(* ------------------------------------------------------------------------ *)
(* Tangent                                                                  *)
(* ------------------------------------------------------------------------ *)

let tan = new_definition
  `tan(x) = sin(x) / cos(x)`;;

let TAN_0 = `tan(&0) = &0`;;

let TAN_PI = `tan(pi) = &0`;;

let TAN_NPI = `!n. tan(&n * pi) = &0`;;

let TAN_NEG = `!x. tan(--x) = --(tan x)`;;

let TAN_PERIODIC = `!x. tan(x + &2 * pi) = tan(x)`;;

let TAN_PERIODIC_PI = `!x. tan(x + pi) = tan(x)`;;

let TAN_PERIODIC_NPI = `!x n. tan(x + &n * pi) = tan(x)`;;

let TAN_ADD = `!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x + y) = &0) ==>
           (tan(x + y) = (tan(x) + tan(y)) / (&1 - tan(x) * tan(y)))`;;

let TAN_DOUBLE = `!x. ~(cos(x) = &0) /\ ~(cos(&2 * x) = &0) ==>
            (tan(&2 * x) = (&2 * tan(x)) / (&1 - (tan(x) pow 2)))`;;

let TAN_POS_PI2 = `!x. &0 < x /\ x < pi / &2 ==> &0 < tan(x)`;;

let DIFF_TAN = `!x. ~(cos(x) = &0) ==> (tan diffl inv(cos(x) pow 2))(x)`;;

let DIFF_TAN_COMPOSITE = `(g diffl m)(x) /\ ~(cos(g x) = &0)
   ==> ((\x. tan(g x)) diffl (inv(cos(g x) pow 2) * m))(x)`;;

let TAN_TOTAL_POS = `!y. &0 <= y ==> ?x. &0 <= x /\ x < pi / &2 /\ (tan(x) = y)`;;

let TAN_TOTAL = `!y. ?!x. --(pi / &2) < x /\ x < (pi / &2) /\ (tan(x) = y)`;;

let PI2_PI4 = `pi / &2 = &2 * pi / &4`;;

let TAN_PI4 = `tan(pi / &4) = &1`;;

let TAN_COT = `!x. tan(pi / &2 - x) = inv(tan x)`;;

let TAN_BOUND_PI2 = `!x. abs(x) < pi / &4 ==> abs(tan x) < &1`;;

let TAN_ABS_GE_X = `!x. abs(x) < pi / &2 ==> abs(x) <= abs(tan x)`;;

(* ------------------------------------------------------------------------ *)
(* Inverse trig functions                                                   *)
(* ------------------------------------------------------------------------ *)

let asn = new_definition
  `asn(y) = @x. --(pi / &2) <= x /\ x <= pi / &2 /\ (sin x = y)`;;

let acs = new_definition
  `acs(y) = @x. &0 <= x /\ x <= pi /\ (cos x = y)`;;

let atn = new_definition
  `atn(y) = @x. --(pi / &2) < x /\ x < pi / &2 /\ (tan x = y)`;;

let ASN = `!y. --(&1) <= y /\ y <= &1 ==>
     --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2 /\ (sin(asn y) = y)`;;

let ASN_SIN = `!y. --(&1) <= y /\ y <= &1 ==> (sin(asn(y)) = y)`;;

let ASN_BOUNDS = `!y. --(&1) <= y /\ y <= &1 ==> --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2`;;

let ASN_BOUNDS_LT = `!y. --(&1) < y /\ y < &1 ==> --(pi / &2) < asn(y) /\ asn(y) < pi / &2`;;

let SIN_ASN = `!x. --(pi / &2) <= x /\ x <= pi / &2 ==> (asn(sin(x)) = x)`;;

let ACS = `!y. --(&1) <= y /\ y <= &1 ==>
     &0 <= acs(y) /\ acs(y) <= pi  /\ (cos(acs y) = y)`;;

let ACS_COS = `!y. --(&1) <= y /\ y <= &1 ==> (cos(acs(y)) = y)`;;

let ACS_BOUNDS = `!y. --(&1) <= y /\ y <= &1 ==> &0 <= acs(y) /\ acs(y) <= pi`;;

let ACS_BOUNDS_LT = `!y. --(&1) < y /\ y < &1 ==> &0 < acs(y) /\ acs(y) < pi`;;

let COS_ACS = `!x. &0 <= x /\ x <= pi ==> (acs(cos(x)) = x)`;;

let ATN = `!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2) /\ (tan(atn y) = y)`;;

let ATN_TAN = `!y. tan(atn y) = y`;;

let ATN_BOUNDS = `!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2)`;;

let TAN_ATN = `!x. --(pi / &2) < x /\ x < (pi / &2) ==> (atn(tan(x)) = x)`;;

let ATN_0 = `atn(&0) = &0`;;

let ATN_1 = `atn(&1) = pi / &4`;;

let ATN_NEG = `!x. atn(--x) = --(atn x)`;;

(* ------------------------------------------------------------------------- *)
(* Differentiation of arctan.                                                *)
(* ------------------------------------------------------------------------- *)

let COS_ATN_NZ = `!x. ~(cos(atn(x)) = &0)`;;

let TAN_SEC = `!x. ~(cos(x) = &0) ==> (&1 + (tan(x) pow 2) = inv(cos x) pow 2)`;;

let DIFF_ATN = `!x. (atn diffl (inv(&1 + (x pow 2))))(x)`;;

let DIFF_ATN_COMPOSITE = `(g diffl m)(x) ==> ((\x. atn(g x)) diffl (inv(&1 + (g x) pow 2) * m))(x)`;;

let ATN_MONO_LT_EQ = `!x y. atn(x) < atn(y) <=> x < y`;;

let ATN_MONO_LE_EQ = `!x y. atn(x) <= atn(y) <=> x <= y`;;

let ATN_INJ = `!x y. (atn x = atn y) <=> (x = y)`;;

let ATN_POS_LT = `&0 < atn(x) <=> &0 < x`;;

let ATN_POS_LE = `&0 <= atn(x) <=> &0 <= x`;;

let ATN_LT_PI4_POS = `!x. x < &1 ==> atn(x) < pi / &4`;;

let ATN_LT_PI4_NEG = `!x. --(&1) < x ==> --(pi / &4) < atn(x)`;;

let ATN_LT_PI4 = `!x. abs(x) < &1 ==> abs(atn x) < pi / &4`;;

let ATN_LE_PI4 = `!x. abs(x) <= &1 ==> abs(atn x) <= pi / &4`;;

(* ------------------------------------------------------------------------- *)
(* Differentiation of arcsin.                                                *)
(* ------------------------------------------------------------------------- *)

let COS_SIN_SQRT = `!x. &0 <= cos(x) ==> (cos(x) = sqrt(&1 - (sin(x) pow 2)))`;;

let COS_ASN_NZ = `!x. --(&1) < x /\ x < &1 ==> ~(cos(asn(x)) = &0)`;;

let DIFF_ASN_COS = `!x. --(&1) < x /\ x < &1 ==> (asn diffl (inv(cos(asn x))))(x)`;;

let DIFF_ASN = `!x. --(&1) < x /\ x < &1 ==> (asn diffl (inv(sqrt(&1 - (x pow 2)))))(x)`;;

let DIFF_ASN_COMPOSITE = `(g diffl m)(x) /\ -- &1 < g(x) /\ g(x) < &1
   ==> ((\x. asn(g x)) diffl (inv(sqrt (&1 - g(x) pow 2)) * m))(x)`;;

let SIN_ACS_NZ = `!x. --(&1) < x /\ x < &1 ==> ~(sin(acs(x)) = &0)`;;

let DIFF_ACS_SIN = `!x. --(&1) < x /\ x < &1 ==> (acs diffl (inv(--(sin(acs x)))))(x)`;;

let DIFF_ACS = `!x. --(&1) < x /\ x < &1 ==> (acs diffl --(inv(sqrt(&1 - (x pow 2)))))(x)`;;

let DIFF_ACS_COMPOSITE = `(g diffl m)(x) /\ -- &1 < g(x) /\ g(x) < &1
   ==> ((\x. acs(g x)) diffl (--inv(sqrt(&1 - g(x) pow 2)) * m))(x)`;;

(* ------------------------------------------------------------------------- *)
(* More lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let ACS_MONO_LT = `!x y. --(&1) < x /\ x < y /\ y < &1 ==> acs(y) < acs(x)`;;

(* ======================================================================== *)
(* Formalization of Kurzweil-Henstock gauge integral                        *)
(* ======================================================================== *)

let LE_MATCH_TAC th (asl,w) =
  let thi = PART_MATCH (rand o rator) th (rand(rator w)) in
  let tm = rand(concl thi) in
  (MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC THENL
    [MATCH_ACCEPT_TAC th; ALL_TAC]) (asl,w);;

(* ------------------------------------------------------------------------ *)
(* Some miscellaneous lemmas                                                *)
(* ------------------------------------------------------------------------ *)

let LESS_SUC_EQ = `!m n. m < SUC n <=> m <= n`;;

let LESS_1 = `!n. n < 1 <=> (n = 0)`;;

(* ------------------------------------------------------------------------ *)
(* Divisions and tagged divisions etc.                                      *)
(* ------------------------------------------------------------------------ *)

let division = new_definition
  `division(a,b) D <=>
     (D 0 = a) /\
     (?N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = b)))`;;

let dsize = new_definition
  `dsize D =
      @N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = D(N)))`;;

let tdiv = new_definition
  `tdiv(a,b) (D,p) <=>
     division(a,b) D /\
     (!n. D(n) <= p(n) /\ p(n) <= D(SUC n))`;;

(* ------------------------------------------------------------------------ *)
(* Gauges and gauge-fine divisions                                          *)
(* ------------------------------------------------------------------------ *)

let gauge = new_definition
  `gauge(E) (g:real->real) <=> !x. E x ==> &0 < g(x)`;;

let fine = new_definition
  `fine(g:real->real) (D,p) <=>
     !n. n < (dsize D) ==> (D(SUC n) - D(n)) < g(p(n))`;;

(* ------------------------------------------------------------------------ *)
(* Riemann sum                                                              *)
(* ------------------------------------------------------------------------ *)

let rsum = new_definition
  `rsum (D,(p:num->real)) f =
        sum(0,dsize(D))(\n. f(p n) * (D(SUC n) - D(n)))`;;

(* ------------------------------------------------------------------------ *)
(* Gauge integrability (definite)                                           *)
(* ------------------------------------------------------------------------ *)

let defint = new_definition
  `defint(a,b) f k <=>
     !e. &0 < e ==>
        ?g. gauge(\x. a <= x /\ x <= b) g /\
            !D p. tdiv(a,b) (D,p) /\ fine(g)(D,p) ==>
                abs(rsum(D,p) f - k) < e`;;

(* ------------------------------------------------------------------------ *)
(* Useful lemmas about the size of `trivial` divisions etc.                 *)
(* ------------------------------------------------------------------------ *)

let DIVISION_0 = `!a b. (a = b) ==> (dsize(\n. if (n = 0) then a else b) = 0)`;;

let DIVISION_1 = `!a b. a < b ==> (dsize(\n. if (n = 0) then a else b) = 1)`;;

let DIVISION_SINGLE = `!a b. a <= b ==> division(a,b)(\n. if (n = 0) then a else b)`;;

let DIVISION_LHS = `!D a b. division(a,b) D ==> (D(0) = a)`;;

let DIVISION_THM = `!D a b. division(a,b) D <=>
        (D(0) = a) /\
        (!n. n < (dsize D) ==> D(n) < D(SUC n)) /\
        (!n. n >= (dsize D) ==> (D(n) = b))`;;

let DIVISION_RHS = `!D a b. division(a,b) D ==> (D(dsize D) = b)`;;

let DIVISION_LT_GEN = `!D a b m n. division(a,b) D /\
               m < n /\
               n <= (dsize D) ==> D(m) < D(n)`;;

let DIVISION_LT = `!D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(0) < D(SUC n)`;;

let DIVISION_LE = `!D a b. division(a,b) D ==> a <= b`;;

let DIVISION_GT = `!D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(n) < D(dsize D)`;;

let DIVISION_EQ = `!D a b. division(a,b) D ==> ((a = b) <=> (dsize D = 0))`;;

let DIVISION_LBOUND = `!D a b r. division(a,b) D ==> a <= D(r)`;;

let DIVISION_LBOUND_LT = `!D a b n. division(a,b) D /\ ~(dsize D = 0) ==> a < D(SUC n)`;;

let DIVISION_UBOUND = `!D a b r. division(a,b) D ==> D(r) <= b`;;

let DIVISION_UBOUND_LT = `!D a b n. division(a,b) D /\
             n < dsize D ==> D(n) < b`;;

(* ------------------------------------------------------------------------ *)
(* Divisions of adjacent intervals can be combined into one                 *)
(* ------------------------------------------------------------------------ *)

let DIVISION_APPEND_LEMMA1 = `!a b c D1 D2. division(a,b) D1 /\ division(b,c) D2 ==>
        (!n. n < ((dsize D1) + (dsize D2)) ==>
                (\n. if (n < (dsize D1)) then  D1(n) else
                     D2(n - (dsize D1)))(n) <
   (\n. if (n < (dsize D1)) then  D1(n) else D2(n - (dsize D1)))(SUC n)) /\
        (!n. n >= ((dsize D1) + (dsize D2)) ==>
               ((\n. if (n < (dsize D1)) then  D1(n) else
   D2(n - (dsize D1)))(n) = (\n. if (n < (dsize D1)) then  D1(n) else
   D2(n - (dsize D1)))((dsize D1) + (dsize D2))))`;;

let DIVISION_APPEND_LEMMA2 = `!a b c D1 D2. division(a,b) D1 /\ division(b,c) D2 ==>
                   (dsize(\n. if (n < (dsize D1)) then  D1(n) else
       D2(n - (dsize D1))) = dsize(D1) + dsize(D2))`;;

let DIVISION_APPEND_EXPLICIT = `!a b c g d1 p1 d2 p2.
        tdiv(a,b) (d1,p1) /\
        fine g (d1,p1) /\
        tdiv(b,c) (d2,p2) /\
        fine g (d2,p2)
        ==> tdiv(a,c)
              ((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
               (\n. if n < dsize d1
                    then p1(n) else p2(n - (dsize d1)))) /\
            fine g ((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
               (\n. if n < dsize d1
                    then p1(n) else p2(n - (dsize d1)))) /\
            !f. rsum((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
                     (\n. if n < dsize d1
                          then p1(n) else p2(n - (dsize d1)))) f =
                rsum(d1,p1) f + rsum(d2,p2) f`;;

let DIVISION_APPEND_STRONG = `!a b c D1 p1 D2 p2.
        tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1) /\
        tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)
        ==> ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p) /\
                  !f. rsum(D,p) f = rsum(D1,p1) f + rsum(D2,p2) f`;;

let DIVISION_APPEND = `!a b c.
      (?D1 p1. tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1)) /\
      (?D2 p2. tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)) ==>
        ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p)`;;

(* ------------------------------------------------------------------------ *)
(* We can always find a division which is fine wrt any gauge                *)
(* ------------------------------------------------------------------------ *)

let DIVISION_EXISTS = `!a b g. a <= b /\ gauge(\x. a <= x /\ x <= b) g ==>
        ?D p. tdiv(a,b) (D,p) /\ fine(g) (D,p)`;;

(* ------------------------------------------------------------------------ *)
(* Lemmas about combining gauges                                            *)
(* ------------------------------------------------------------------------ *)

let GAUGE_MIN = `!E g1 g2. gauge(E) g1 /\ gauge(E) g2 ==>
        gauge(E) (\x. if g1(x) < g2(x) then g1(x) else g2(x))`;;

let FINE_MIN = `!g1 g2 D p. fine (\x. if g1(x) < g2(x) then g1(x) else g2(x)) (D,p) ==>
        fine(g1) (D,p) /\ fine(g2) (D,p)`;;

(* ------------------------------------------------------------------------ *)
(* The integral is unique if it exists                                      *)
(* ------------------------------------------------------------------------ *)

let DINT_UNIQ = `!a b f k1 k2. a <= b /\ defint(a,b) f k1 /\ defint(a,b) f k2 ==> (k1 = k2)`;;

(* ------------------------------------------------------------------------ *)
(* Integral over a null interval is 0                                       *)
(* ------------------------------------------------------------------------ *)

let INTEGRAL_NULL = `!f a. defint(a,a) f (&0)`;;

(* ------------------------------------------------------------------------ *)
(* Fundamental theorem of calculus (Part I)                                 *)
(* ------------------------------------------------------------------------ *)

let STRADDLE_LEMMA = `!f f' a b e. (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\ &0 < e
    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
            !x u v. a <= u /\ u <= x /\ x <= v /\ v <= b /\ (v - u) < g(x)
                ==> abs((f(v) - f(u)) - (f'(x) * (v - u))) <= e * (v - u)`;;

let FTC1 = `!f f' a b. a <= b /\ (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x))
        ==> defint(a,b) f' (f(b) - f(a))`;;

(* ------------------------------------------------------------------------- *)
(* Definition of integral and integrability.                                 *)
(* ------------------------------------------------------------------------- *)

let integrable = new_definition
 `integrable(a,b) f = ?i. defint(a,b) f i`;;

let integral = new_definition
 `integral(a,b) f = @i. defint(a,b) f i`;;

let INTEGRABLE_DEFINT = `!f a b. integrable(a,b) f ==> defint(a,b) f (integral(a,b) f)`;;

(* ------------------------------------------------------------------------- *)
(* Other more or less trivial lemmas.                                        *)
(* ------------------------------------------------------------------------- *)

let DIVISION_BOUNDS = `!d a b. division(a,b) d ==> !n. a <= d(n) /\ d(n) <= b`;;

let TDIV_BOUNDS = `!d p a b. tdiv(a,b) (d,p)
             ==> !n. a <= d(n) /\ d(n) <= b /\ a <= p(n) /\ p(n) <= b`;;

let TDIV_LE = `!d p a b. tdiv(a,b) (d,p) ==> a <= b`;;

let DEFINT_WRONG = `!a b f i. b < a ==> defint(a,b) f i`;;

let DEFINT_INTEGRAL = `!f a b i. a <= b /\ defint(a,b) f i ==> integral(a,b) f = i`;;

(* ------------------------------------------------------------------------- *)
(* Linearity.                                                                *)
(* ------------------------------------------------------------------------- *)

let DEFINT_CONST = `!a b c. defint(a,b) (\x. c) (c * (b - a))`;;

let DEFINT_0 = `!a b. defint(a,b) (\x. &0) (&0)`;;

let DEFINT_NEG = `!f a b i. defint(a,b) f i ==> defint(a,b) (\x. --f x) (--i)`;;

let DEFINT_CMUL = `!f a b c i. defint(a,b) f i ==> defint(a,b) (\x. c * f x) (c * i)`;;

let DEFINT_ADD = `!f g a b i j.
        defint(a,b) f i /\ defint(a,b) g j
        ==> defint(a,b) (\x. f x + g x) (i + j)`;;

let DEFINT_SUB = `!f g a b i j.
        defint(a,b) f i /\ defint(a,b) g j
        ==> defint(a,b) (\x. f x - g x) (i - j)`;;

(* ------------------------------------------------------------------------- *)
(* Ordering properties of integral.                                          *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_LE = `!f g a b i j.
        a <= b /\ integrable(a,b) f /\ integrable(a,b) g /\
        (!x. a <= x /\ x <= b ==> f(x) <= g(x))
        ==> integral(a,b) f <= integral(a,b) g`;;

let DEFINT_LE = `!f g a b i j. a <= b /\ defint(a,b) f i /\ defint(a,b) g j /\
                 (!x. a <= x /\ x <= b ==> f(x) <= g(x))
                 ==> i <= j`;;

let DEFINT_TRIANGLE = `!f a b i j. a <= b /\ defint(a,b) f i /\ defint(a,b) (\x. abs(f x)) j
               ==> abs(i) <= j`;;

let DEFINT_EQ = `!f g a b i j. a <= b /\ defint(a,b) f i /\ defint(a,b) g j /\
                 (!x. a <= x /\ x <= b ==> f(x) = g(x))
                 ==> i = j`;;

let INTEGRAL_EQ = `!f g a b i. defint(a,b) f i /\
               (!x. a <= x /\ x <= b ==> f(x) = g(x))
               ==> defint(a,b) g i`;;

(* ------------------------------------------------------------------------- *)
(* Integration by parts.                                                     *)
(* ------------------------------------------------------------------------- *)

let INTEGRATION_BY_PARTS = `!f g f' g' a b.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        (!x. a <= x /\ x <= b ==> (g diffl g'(x))(x))
        ==> defint(a,b) (\x. f'(x) * g(x) + f(x) * g'(x))
                        (f(b) * g(b) - f(a) * g(a))`;;

(* ------------------------------------------------------------------------- *)
(* Various simple lemmas about divisions.                                    *)
(* ------------------------------------------------------------------------- *)

let DIVISION_LE_SUC = `!d a b. division(a,b) d ==> !n. d(n) <= d(SUC n)`;;

let DIVISION_MONO_LE = `!d a b. division(a,b) d ==> !m n. m <= n ==> d(m) <= d(n)`;;

let DIVISION_MONO_LE_SUC = `!d a b. division(a,b) d ==> !n. d(n) <= d(SUC n)`;;

let DIVISION_INTERMEDIATE = `!d a b c. division(a,b) d /\ a <= c /\ c <= b
             ==> ?n. n <= dsize d /\ d(n) <= c /\ c <= d(SUC n)`;;

let DIVISION_DSIZE_LE = `!a b d n. division(a,b) d /\ d(SUC n) = d(n) ==> dsize d <= n`;;

let DIVISION_DSIZE_GE = `!a b d n. division(a,b) d /\ d(n) < d(SUC n) ==> SUC n <= dsize d`;;

let DIVISION_DSIZE_EQ = `!a b d n. division(a,b) d /\ d(n) < d(SUC n) /\ d(SUC(SUC n)) = d(SUC n)
           ==> dsize d = SUC n`;;

let DIVISION_DSIZE_EQ_ALT = `!a b d n. division(a,b) d /\ d(SUC n) = d(n) /\
             (!i. i < n ==> d(i) < d(SUC i))
             ==> dsize d = n`;;

(* ------------------------------------------------------------------------- *)
(* Combination of adjacent intervals (quite painful in the details).         *)
(* ------------------------------------------------------------------------- *)

let DEFINT_COMBINE = `!f a b c i j. a <= b /\ b <= c /\ defint(a,b) f i /\ defint(b,c) f j
                 ==> defint(a,c) f (i + j)`;;

(* ------------------------------------------------------------------------- *)
(* Pointwise perturbation and spike functions.                               *)
(* ------------------------------------------------------------------------- *)

let DEFINT_DELTA_LEFT = `!a b. defint(a,b) (\x. if x = a then &1 else &0) (&0)`;;

let DEFINT_DELTA_RIGHT = `!a b. defint(a,b) (\x. if x = b then &1 else &0) (&0)`;;

let DEFINT_DELTA = `!a b c. defint(a,b) (\x. if x = c then &1 else &0) (&0)`;;

let DEFINT_POINT_SPIKE = `!f g a b c i.
        (!x. a <= x /\ x <= b /\ ~(x = c) ==> (f x = g x)) /\ defint(a,b) f i
        ==> defint(a,b) g i`;;

let DEFINT_FINITE_SPIKE = `!f g a b s i.
        FINITE s /\
        (!x. a <= x /\ x <= b /\ ~(x IN s) ==> (f x = g x)) /\
        defint(a,b) f i
        ==> defint(a,b) g i`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy-type integrability criterion.                                      *)
(* ------------------------------------------------------------------------- *)

let GAUGE_MIN_FINITE = `!s gs n. (!m:num. m <= n ==> gauge s (gs m))
            ==> ?g. gauge s g /\
                    !d p. fine g (d,p) ==> !m. m <= n ==> fine (gs m) (d,p)`;;

let INTEGRABLE_CAUCHY = `!f a b. integrable(a,b) f <=>
           !e. &0 < e
               ==> ?g. gauge (\x. a <= x /\ x <= b) g /\
                       !d1 p1 d2 p2.
                            tdiv (a,b) (d1,p1) /\ fine g (d1,p1) /\
                            tdiv (a,b) (d2,p2) /\ fine g (d2,p2)
                            ==> abs (rsum(d1,p1) f - rsum(d2,p2) f) < e`;;

(* ------------------------------------------------------------------------- *)
(* Limit theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

let SUM_DIFFS = `!m n. sum(m,n) (\i. d(SUC i) - d(i)) = d(m + n) - d m`;;

let RSUM_BOUND = `!a b d p e f.
        tdiv(a,b) (d,p) /\
        (!x. a <= x /\ x <= b ==> abs(f x) <= e)
        ==> abs(rsum(d,p) f) <= e * (b - a)`;;

let RSUM_DIFF_BOUND = `!a b d p e f g.
        tdiv(a,b) (d,p) /\
        (!x. a <= x /\ x <= b ==> abs(f x - g x) <= e)
        ==> abs(rsum (d,p) f - rsum (d,p) g) <= e * (b - a)`;;

let INTEGRABLE_LIMIT = `!f a b. (!e. &0 < e
                ==> ?g. (!x. a <= x /\ x <= b ==> abs(f x - g x) <= e) /\
                        integrable(a,b) g)
           ==> integrable(a,b) f`;;

(* ------------------------------------------------------------------------- *)
(* Hence continuous functions are integrable.                                *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_CONST = `!a b c. integrable(a,b) (\x. c)`;;

let INTEGRABLE_COMBINE = `!f a b c. a <= b /\ b <= c /\ integrable(a,b) f /\ integrable(b,c) f
         ==> integrable(a,c) f`;;

let INTEGRABLE_POINT_SPIKE = `!f g a b c.
         (!x. a <= x /\ x <= b /\ ~(x = c) ==> f x = g x) /\ integrable(a,b) f
         ==> integrable(a,b) g`;;

let INTEGRABLE_CONTINUOUS = `!f a b. (!x. a <= x /\ x <= b ==> f contl x) ==> integrable(a,b) f`;;

(* ------------------------------------------------------------------------- *)
(* Integrability on a subinterval.                                           *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_SPLIT_SIDES = `!f a b c.
        a <= c /\ c <= b /\ integrable(a,b) f
        ==> ?i. !e. &0 < e
                    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
                            !d1 p1 d2 p2. tdiv(a,c) (d1,p1) /\
                                          fine g (d1,p1) /\
                                          tdiv(c,b) (d2,p2) /\
                                          fine g (d2,p2)
                                          ==> abs((rsum(d1,p1) f +
                                                   rsum(d2,p2) f) - i) < e`;;

let INTEGRABLE_SUBINTERVAL_LEFT = `!f a b c. a <= c /\ c <= b /\ integrable(a,b) f ==> integrable(a,c) f`;;

let INTEGRABLE_SUBINTERVAL_RIGHT = `!f a b c. a <= c /\ c <= b /\ integrable(a,b) f ==> integrable(c,b) f`;;

let INTEGRABLE_SUBINTERVAL = `!f a b c d. a <= c /\ c <= d /\ d <= b /\ integrable(a,b) f
               ==> integrable(c,d) f`;;

(* ------------------------------------------------------------------------- *)
(* Basic integrability rule for everywhere-differentiable function.          *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_RULE =
  let pth = `(!x. f contl x) ==> integrable(a,b) f`;;

let INTEGRAL_CMUL = `!f c a b. a <= b /\ integrable(a,b) f
             ==> integral(a,b) (\x. c * f(x)) = c * integral(a,b) f`;;

let INTEGRAL_ADD = `!f g a b. a <= b /\ integrable(a,b) f /\ integrable(a,b) g
             ==> integral(a,b) (\x. f(x) + g(x)) =
                 integral(a,b) f + integral(a,b) g`;;

let INTEGRAL_SUB = `!f g a b. a <= b /\ integrable(a,b) f /\ integrable(a,b) g
             ==> integral(a,b) (\x. f(x) - g(x)) =
                 integral(a,b) f - integral(a,b) g`;;

let INTEGRAL_BY_PARTS = `!f g f' g' a b.
         a <= b /\
         (!x. a <= x /\ x <= b ==> (f diffl f' x) x) /\
         (!x. a <= x /\ x <= b ==> (g diffl g' x) x) /\
         integrable(a,b) (\x. f' x * g x) /\
         integrable(a,b) (\x. f x * g' x)
         ==> integral(a,b) (\x. f x * g' x) =
             (f b * g b - f a * g a) - integral(a,b) (\x. f' x * g x)`;;

(* ------------------------------------------------------------------------ *)
(* SYM_CANON_CONV - Canonicalizes single application of symmetric operator  *)
(* Rewrites `so as to make fn true`, e.g. fn = (<<) or fn = (=) `1` o fst   *)
(* ------------------------------------------------------------------------ *)

let SYM_CANON_CONV sym fn =
  REWR_CONV sym o check
   (not o fn o ((snd o dest_comb) F_F I) o dest_comb);;

(* ----------------------------------------------------------- *)
(* EXT_CONV `!x. f x = g x` = |- (!x. f x = g x) <=> (f = g)   *)
(* ----------------------------------------------------------- *)

let EXT_CONV =  SYM o uncurry X_FUN_EQ_CONV o
      (I F_F (mk_eq o (rator F_F rator) o dest_eq)) o dest_forall;;

(* ------------------------------------------------------------------------ *)
(* Mclaurin's theorem with Lagrange form of remainder                       *)
(* We could weaken the hypotheses slightly, but it's not worth it           *)
(* ------------------------------------------------------------------------ *)

let MCLAURIN = `!f diff h n.
    &0 < h /\
    0 < n /\
    (diff(0) = f) /\
    (!m t. m < n /\ &0 <= t /\ t <= h ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
   (?t. &0 < t /\ t < h /\
        (f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)) +
                ((diff(n)(t) / &(FACT n)) * (h pow n))))`;;

let MCLAURIN_NEG = `!f diff h n.
    h < &0 /\
    0 < n /\
    (diff(0) = f) /\
    (!m t. m < n /\ h <= t /\ t <= &0 ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
   (?t. h < t /\ t < &0 /\
        (f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)) +
                ((diff(n)(t) / &(FACT n)) * (h pow n))))`;;

(* ------------------------------------------------------------------------- *)
(* More convenient "bidirectional" version.                                  *)
(* ------------------------------------------------------------------------- *)

let MCLAURIN_BI_LE = `!f diff x n.
        (diff 0 = f) /\
        (!m t. m < n /\ abs(t) <= abs(x) ==> (diff m diffl diff (SUC m) t) t)
        ==> ?t. abs(t) <= abs(x) /\
                (f x = sum (0,n) (\m. diff m (&0) / &(FACT m) * x pow m) +
                       diff n t / &(FACT n) * x pow n)`;;

(* ------------------------------------------------------------------------- *)
(* Simple strong form if a function is differentiable everywhere.            *)
(* ------------------------------------------------------------------------- *)

let MCLAURIN_ALL_LT = `!f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ~(x = &0) /\ 0 < n
            ==> ?t. &0 < abs(t) /\ abs(t) < abs(x) /\
                    (f(x) = sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) +
                            (diff n t / &(FACT n)) * x pow n)`;;

let MCLAURIN_ZERO = `!diff n x. (x = &0) /\ 0 < n ==>
       (sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) = diff 0 (&0))`;;

let MCLAURIN_ALL_LE = `!f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ?t. abs(t) <= abs(x) /\
                    (f(x) = sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) +
                            (diff n t / &(FACT n)) * x pow n)`;;

(* ------------------------------------------------------------------------- *)
(* Version for exp.                                                          *)
(* ------------------------------------------------------------------------- *)

let MCLAURIN_EXP_LEMMA = `((\n:num. exp) 0 = exp) /\
   (!m x. (((\n:num. exp) m) diffl ((\n:num. exp) (SUC m) x)) x)`;;

let MCLAURIN_EXP_LT = `!x n. ~(x = &0) /\ 0 < n
         ==> ?t. &0 < abs(t) /\
                 abs(t) < abs(x) /\
                 (exp(x) = sum(0,n)(\m. x pow m / &(FACT m)) +
                           (exp(t) / &(FACT n)) * x pow n)`;;

let MCLAURIN_EXP_LE = `!x n. ?t. abs(t) <= abs(x) /\
             (exp(x) = sum(0,n)(\m. x pow m / &(FACT m)) +
                       (exp(t) / &(FACT n)) * x pow n)`;;

(* ------------------------------------------------------------------------- *)
(* Version for ln(1 +/- x).                                                  *)
(* ------------------------------------------------------------------------- *)

let DIFF_LN_COMPOSITE = `!g m x. (g diffl m)(x) /\ &0 < g x
           ==> ((\x. ln(g x)) diffl (inv(g x) * m))(x)`;;

let MCLAURIN_LN_POS = `!x n.
     &0 < x /\ 0 < n
     ==> ?t. &0 < t /\
             t < x /\
             (ln(&1 + x) = sum(0,n)
                           (\m. --(&1) pow (SUC m) * (x pow m) / &m) +
               --(&1) pow (SUC n) * x pow n / (&n * (&1 + t) pow n))`;;

let MCLAURIN_LN_NEG = `!x n. &0 < x /\ x < &1 /\ 0 < n
         ==> ?t. &0 < t /\
                 t < x /\
                 (--(ln(&1 - x)) = sum(0,n) (\m. (x pow m) / &m) +
                                    x pow n / (&n * (&1 - t) pow n))`;;

(* ------------------------------------------------------------------------- *)
(* Versions for sin and cos.                                                 *)
(* ------------------------------------------------------------------------- *)

let MCLAURIN_SIN = `!x n. abs(sin x -
             sum(0,n) (\m. (if EVEN m then &0
                            else -- &1 pow ((m - 1) DIV 2) / &(FACT m)) *
                            x pow m))
         <= inv(&(FACT n)) * abs(x) pow n`;;

let MCLAURIN_COS = `!x n. abs(cos x -
                   sum(0,n) (\m. (if EVEN m
                                  then -- &1 pow (m DIV 2) / &(FACT m)
                                  else &0) * x pow m))
               <= inv(&(FACT n)) * abs(x) pow n`;;

(* ------------------------------------------------------------------------- *)
(* Taylor series for atan; needs a bit more preparation.                     *)
(* ------------------------------------------------------------------------- *)

let REAL_ATN_POWSER_SUMMABLE = `!x. abs(x) < &1
       ==> summable (\n. (if EVEN n then &0
                          else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n)`;;

let REAL_ATN_POWSER_DIFFS_SUMMABLE = `!x. abs(x) < &1
       ==> summable (\n. diffs (\n. (if EVEN n then &0
                                     else --(&1) pow ((n - 1) DIV 2) / &n)) n *
                         x pow n)`;;

let REAL_ATN_POWSER_DIFFS_SUM = `!x. abs(x) < &1
       ==> (\n. diffs (\n. (if EVEN n then &0
                            else --(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)
           sums (inv(&1 + x pow 2))`;;

let REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE = `!x. abs(x) < &1
       ==> summable
             (\n. diffs (diffs
                 (\n. (if EVEN n then &0
                       else --(&1) pow ((n - 1) DIV 2) / &n))) n * x pow n)`;;

let REAL_ATN_POWSER_DIFFL = `!x. abs(x) < &1
       ==> ((\x. suminf (\n. (if EVEN n then &0
                              else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n))
            diffl (inv(&1 + x pow 2))) x`;;

let REAL_ATN_POWSER = `!x. abs(x) < &1
       ==> (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n)
           sums (atn x)`;;

let MCLAURIN_ATN = `!x n. abs(x) < &1
           ==> abs(atn x -
                   sum(0,n) (\m. (if EVEN m then &0
                                  else --(&1) pow ((m - 1) DIV 2) / &m) *
                                  x pow m))
               <= abs(x) pow n / (&1 - abs x)`;;
