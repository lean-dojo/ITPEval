(* ========================================================================= *)
(* Proof of Bertrand conjecture and weak form of prime number theorem.       *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/pocklington.ml";;
needs "Library/analysis.ml";;
needs "Library/transc.ml";;
needs "Library/calc_real.ml";;
needs "Library/floor.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* A ridiculous ommission from the OCaml Num library.                        *)
(* ------------------------------------------------------------------------- *)

let num_of_float =
  let p22 = ( ** ) 2.0 22.0
  and p44 = ( ** ) 2.0 44.0
  and p66 = ( ** ) 2.0 66.0
  and q22 = pow2 22 and q44 = pow2 44 and q66 = pow2 66 in
  fun x ->
    let y0,n = frexp x in
    let u0 = int_of_float(y0 *. p22) in
    let y1 = p22 *. y0 -. float_of_int u0 in
    let u1 = int_of_float(y1 *. p22) in
    let y2 = p22 *. y1 -. float_of_int u1 in
    let u2 = int_of_float(y2 *. p22) in
    let y3 = p22 *. y2 -. float_of_int u2 in
    if y3 <> 0.0 then failwith "num_of_float: inexactness!" else
    (num u0 // q22 +/ num u1 // q44 +/ num u2 // q66) */ pow2 n;;

(* ------------------------------------------------------------------------- *)
(* Integer truncated square root                                             *)
(* ------------------------------------------------------------------------- *)

let ISQRT = new_definition
  `ISQRT n = @m. m EXP 2 <= n /\ n < (m + 1) EXP 2`;;

let ISQRT_WORKS = `!n. ISQRT(n) EXP 2 <= n /\ n < (ISQRT(n) + 1) EXP 2`;;

let ISQRT_0 = `ISQRT 0 = 0`;;

let ISQRT_UNIQUE = `!m n. (ISQRT n = m) <=> m EXP 2 <= n /\ n < (m + 1) EXP 2`;;

let ISQRT_SUC = `!n. ISQRT(SUC n) =
       if ?m. SUC n = m EXP 2 then SUC(ISQRT n) else ISQRT n`;;

(* ------------------------------------------------------------------------- *)
(* To allow us to deal with ln(2) numerically using standard conversion.     *)
(* ------------------------------------------------------------------------- *)

let LN_2_COMPOSITION = `ln(&2) =
   &7 * ln(&1 + inv(&8)) - &2 * ln(&1 + inv(&24)) - &4 * ln(&1 + inv(&80))`;;

(* ------------------------------------------------------------------------- *)
(* Automatically process any ln(n) to allow us to use standard conversions.  *)
(* ------------------------------------------------------------------------- *)

let LN_N_CONV =
  let pth = `x = (&1 + inv(&8)) pow n * (x / (&1 + inv(&8)) pow n)`;;

(* ------------------------------------------------------------------------- *)
(* Range bounds on ln(n!).                                                   *)
(* ------------------------------------------------------------------------- *)

let LN_FACT = `!n. ln(&(FACT n)) = sum(1,n) (\d. ln(&d))`;;

let LN_FACT_BOUNDS = `!n. ~(n = 0) ==> abs(ln(&(FACT n)) - (&n * ln(&n) - &n)) <= &1 + ln(&n)`;;

(* ------------------------------------------------------------------------- *)
(* Some extra number-theoretic odds and ends are useful.                     *)
(* ------------------------------------------------------------------------- *)

let primepow = new_definition
  `primepow q <=> ?p k. 1 <= k /\ prime p /\ (q = p EXP k)`;;

let aprimedivisor = new_definition
  `aprimedivisor q = @p. prime p /\ p divides q`;;

let PRIMEPOW_GE_2 = `!q. primepow q ==> 2 <= q`;;

let PRIMEPOW_0 = `~(primepow 0)`;;

let APRIMEDIVISOR_PRIMEPOW = `!p k. prime p /\ 1 <= k ==> (aprimedivisor(p EXP k) = p)`;;

let APRIMEDIVISOR = `!n. ~(n = 1) ==> prime(aprimedivisor n) /\ (aprimedivisor n) divides n`;;

let BIG_POWER_LEMMA = `!m n. 2 <= m ==> ?k. n <= m EXP k`;;

let PRIME_PRIMEPOW = `!p. prime p ==> primepow p`;;

(* ------------------------------------------------------------------------- *)
(* Derive Bezout-type identity by finding gcd.                               *)
(* ------------------------------------------------------------------------- *)

let rec bezout (m,n) =
  if m =/ num 0 then (num 0,num 1) else if n =/ num 0 then (num 1,num 0)
  else if m <=/ n then
    let q = quo_num n m and r = mod_num n m in
    let (x,y) = bezout(m,r) in
    (x -/ q */ y,y)
  else let (x,y) = bezout(n,m) in (y,x);;

(* ------------------------------------------------------------------------- *)
(* Conversion for "primepow" applied to particular numeral.                  *)
(* ------------------------------------------------------------------------- *)

let PRIMEPOW_CONV =
  let pth0 = `primepow 0 <=> F`;;

(* ------------------------------------------------------------------------- *)
(* Conversion for "aprimedivisor" applied to prime power (only).             *)
(* ------------------------------------------------------------------------- *)

let APRIMEDIVISOR_CONV =
  let pth = `prime p ==> 1 <= k /\ (q = p EXP k) ==> (aprimedivisor q = p)`;;

(* ------------------------------------------------------------------------- *)
(* The key lemma.                                                            *)
(* ------------------------------------------------------------------------- *)

let LN_PRIMEFACT = `!n. ~(n = 0)
       ==> (ln(&n) =
            sum(1,n) (\d. if primepow d /\ d divides n
                          then ln(&(aprimedivisor d)) else &0))`;;

(* ------------------------------------------------------------------------- *)
(* The key expansion using the Mangoldt function.                            *)
(* ------------------------------------------------------------------------- *)

let MANGOLDT = `!n. ln(&(FACT n)) = sum(1,n) (\d. mangoldt(d) * floor(&n / &d))`;;

(* ------------------------------------------------------------------------- *)
(* The Chebyshev psi function.                                               *)
(* ------------------------------------------------------------------------- *)

let psi = new_definition
  `psi(n) = sum(1,n) (\d. mangoldt(d))`;;

(* ------------------------------------------------------------------------- *)
(* The key bounds on the psi function.                                       *)
(* ------------------------------------------------------------------------- *)

let PSI_BOUNDS_LN_FACT = `!n. ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2))) <= psi(n) /\
       psi(n) - psi(n DIV 2) <= ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2)))`;;

(* ------------------------------------------------------------------------- *)
(* Map the middle term into multiples of log(n).                             *)
(* ------------------------------------------------------------------------- *)

let LN_FACT_DIFF_BOUNDS = `!n. abs((ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2)))) - &n * ln(&2))
       <= &4 * ln(if n = 0 then &1 else &n) + &3`;;

(* ------------------------------------------------------------------------- *)
(* Hence overall bounds in terms of n * log(2) + constant.                   *)
(* ------------------------------------------------------------------------- *)

let PSI_BOUNDS_INDUCT = `!n. &n * ln(&2) - (&4 * ln (if n = 0 then &1 else &n) + &3) <= psi(n) /\
       psi(n) - psi(n DIV 2)
       <= &n * ln(&2) + (&4 * ln (if n = 0 then &1 else &n) + &3)`;;

(* ------------------------------------------------------------------------- *)
(* Evaluation of mangoldt(numeral).                                          *)
(* ------------------------------------------------------------------------- *)

let MANGOLDT_CONV =
  GEN_REWRITE_CONV I [mangoldt] THENC
  RATOR_CONV(LAND_CONV PRIMEPOW_CONV) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES] THENC
  TRY_CONV(funpow 2 RAND_CONV APRIMEDIVISOR_CONV);;

(* ------------------------------------------------------------------------- *)
(* More efficient version without two primality tests.                       *)
(* ------------------------------------------------------------------------- *)

let MANGOLDT_CONV =
  let pth0 = `mangoldt 0 = ln(&1)`;;

(* ------------------------------------------------------------------------- *)
(* Hence an evaluation function for psi, applied to all n <= some N.         *)
(* ------------------------------------------------------------------------- *)

let PSI_LIST =
  let PSI_0 = `psi(0) = ln(&1)`;;

(* ------------------------------------------------------------------------- *)
(* As a multiple of log(2) is often more useful.                             *)
(* ------------------------------------------------------------------------- *)

let PSI_UBOUND_128_LOG = `!n. n <= 128 ==> psi(n) <= (&3 / &2 * ln(&2)) * &n`;;

(* ------------------------------------------------------------------------- *)
(* Useful "overpowering" lemma.                                              *)
(* ------------------------------------------------------------------------- *)

let OVERPOWER_LEMMA = `!f g d a.
        f(a) <= g(a) /\
        (!x. a <= x ==> ((\x. g(x) - f(x)) diffl (d(x)))(x)) /\
        (!x. a <= x ==> &0 <= d(x))
        ==> !x. a <= x ==> f(x) <= g(x)`;;

(* ------------------------------------------------------------------------- *)
(* Repeatedly extend range of explicit cases using recurrence.               *)
(* ------------------------------------------------------------------------- *)

let DOUBLE_CASES_RULE th =
  let bod = snd(dest_forall(concl th)) in
  let ant,cons = dest_imp bod in
  let m = dest_numeral (rand ant)
  and c = rat_of_term (lhand(lhand(rand cons))) in
  let x = float_of_num(m +/ num 1) in
  let d = (4.0 *. log x +. 3.0) /. (x *. log 2.0) in
  let c' = c // num 2 +/ num 1 +/
           (floor_num(num_of_float(1024.0 *. d)) +/ num 2) // num 1024 in
  let c'' = max_num c c' in
  let tm = mk_forall
   (`n:num`,
    subst [mk_numeral(num 2 */ m),rand ant;
          term_of_rat c'',lhand(lhand(rand cons))] bod) in
  prove(tm,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (mk_comb(`(<=) (n:num)`,mk_numeral m)) THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP th) THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(SPEC `n:num` PSI_BOUNDS_INDUCT) THEN
    SUBGOAL_THEN `~(n = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_ASSUM(UNDISCH_TAC o check is_neg o concl) THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `pn2 <= ((a - &1) * l2) * n - logtm
      ==> u <= v /\ pn - pn2 <= n * l2 + logtm ==> pn <= (a * l2) * n`) THEN
    MP_TAC(SPEC `n DIV 2` th) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LE_LDIV_EQ; ARITH] THEN
      FIRST_ASSUM(UNDISCH_TAC o check ((not) o is_neg) o concl) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    W(fun (asl,w) ->
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC(mk_comb(rator(lhand w),`&n / &2`))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ALL_TAC] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_div] THEN
    MATCH_MP_TAC(REAL_ARITH
     `logtm <= ((c - a * b) * l2) * n
      ==> (a * l2) * n * b <= (c * l2) * n - logtm`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBST1_TAC(REAL_ARITH `&n = &1 + (&n - &1)`) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `~(n <= b) ==> b + 1 <= n`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_OF_NUM_LE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `a <= n ==> a - &1 <= n - &1`)) THEN
    ABBREV_TAC `x = &n - &1` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
    SPEC_TAC(`x:real`,`x:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    MATCH_MP_TAC OVERPOWER_LEMMA THEN
    W(fun (asl,w) ->
        let th = DIFF_CONV
         (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
        MP_TAC th) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
      REAL_MUL_RID; REAL_MUL_LID] THEN
    W(fun (asl,w) ->
        let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
        DISCH_TAC THEN EXISTS_TAC tm) THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_sub] THEN
      CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
      CONV_TAC REALCALC_REL_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
                 inv(&1 + a) <= b ==> inv(&1 + x) <= b`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV);;

(* ------------------------------------------------------------------------- *)
(* Bring it to the self-sustaining point.                                    *)
(* ------------------------------------------------------------------------- *)

let PSI_UBOUND_1024_LOG = funpow 3 DOUBLE_CASES_RULE PSI_UBOUND_128_LOG;;

(* ------------------------------------------------------------------------- *)
(* A generic proof of the same kind that we're self-sustaining.              *)
(* ------------------------------------------------------------------------- *)

let PSI_BOUNDS_SUSTAINED_INDUCT = `&4 * ln(&1 + &2 pow j) + &3 <= (d * ln(&2)) * (&1 + &2 pow j) /\
   &4 / (&1 + &2 pow j) <= d * ln(&2) /\ &0 <= c /\ c / &2 + d + &1 <= c
   ==> !k. j <= k /\
           (!n. n <= 2 EXP k ==> psi(n) <= (c * ln(&2)) * &n)
           ==> !n. n <= 2 EXP (SUC k) ==> psi(n) <= (c * ln(&2)) * &n`;;

let PSI_BOUNDS_SUSTAINED = `(!n. n <= 2 EXP k ==> psi(n) <= (c * ln(&2)) * &n)
   ==> &4 * ln(&1 + &2 pow k) + &3
         <= ((c / &2 - &1) * ln(&2)) * (&1 + &2 pow k) /\
       &4 / (&1 + &2 pow k) <= (c / &2 - &1) * ln(&2) /\ &0 <= c
           ==> !n. psi(n) <= (c * ln(&2)) * &n`;;

(* ------------------------------------------------------------------------- *)
(* Now apply it and get our reasonable bound.                                *)
(* ------------------------------------------------------------------------- *)

let PSI_UBOUND_LOG = `!n. psi(n) <= (&4407 / &2048 * ln (&2)) * &n`;;

let PSI_UBOUND_3_2 = `!n. psi(n) <= &3 / &2 * &n`;;

(* ------------------------------------------------------------------------- *)
(* Now get a lower bound.                                                    *)
(* ------------------------------------------------------------------------- *)

let PSI_LBOUND_3_5 = `!n. 4 <= n ==> &3 / &5 * &n <= psi(n)`;;

(* ========================================================================= *)
(* Now the related theta function.                                           *)
(* ========================================================================= *)

let theta = new_definition
  `theta(n) = sum(1,n) (\p. if prime p then ln(&p) else &0)`;;

(* ------------------------------------------------------------------------- *)
(* An optimized rule to give theta(n) for all n <= some N.                   *)
(* ------------------------------------------------------------------------- *)

let THETA_LIST =
  let THETA_0 = `theta(0) = ln(&1)`;;

let PSI_SPLIT = `psi(n) = theta(n) +
            sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                          then ln(&(aprimedivisor d)) else &0) +
            sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                          then ln(&(aprimedivisor d)) else &0)`;;

(* ------------------------------------------------------------------------- *)
(* General lemma about sums.                                                 *)
(* ------------------------------------------------------------------------- *)

let SUM_SURJECT = `!f i m n p q.
        (!r. m <= r /\ r < m + n ==> &0 <= f(i r)) /\
        (!s. p <= s /\ s < p + q /\ ~(f(s) = &0)
             ==> ?r. m <= r /\ r < m + n /\ (i r = s))
        ==> sum(p,q) f <= sum(m,n) (\r. f(i r))`;;

(* ------------------------------------------------------------------------- *)
(* Apply this to show that one of the residuals is bounded by the other.     *)
(* ------------------------------------------------------------------------- *)

let PSI_RESIDUES_COMPARE_2 = `sum(2,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                 then ln(&(aprimedivisor d)) else &0)
   <= sum(2,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                    then ln(&(aprimedivisor d)) else &0)`;;

let PSI_RESIDUES_COMPARE = `!n. sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                     then ln(&(aprimedivisor d)) else &0)
       <= sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                        then ln(&(aprimedivisor d)) else &0)`;;

(* ------------------------------------------------------------------------- *)
(* The even residual reduces to the square root case.                        *)
(* ------------------------------------------------------------------------- *)

let PSI_SQRT = `!n. psi(ISQRT(n)) =
        sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                      then ln(&(aprimedivisor d)) else &0)`;;

(* ------------------------------------------------------------------------- *)
(* Hence the main comparison result.                                         *)
(* ------------------------------------------------------------------------- *)

let PSI_THETA = `!n. theta(n) + psi(ISQRT n) <= psi(n) /\
       psi(n) <= theta(n) + &2 * psi(ISQRT n)`;;

(* ------------------------------------------------------------------------- *)
(* A trivial one-way comparison is immediate.                                *)
(* ------------------------------------------------------------------------- *)

let THETA_LE_PSI = `!n. theta(n) <= psi(n)`;;

(* ------------------------------------------------------------------------- *)
(* A tighter bound on psi on a smaller range, to reduce later case analysis. *)
(* ------------------------------------------------------------------------- *)

let PSI_UBOUND_30 = `!n. n <= 30 ==> psi(n) <= &65 / &64 * &n`;;

(* ------------------------------------------------------------------------- *)
(* Bounds for theta, derived from those for psi.                             *)
(* ------------------------------------------------------------------------- *)

let THETA_UBOUND_3_2 = `!n. theta(n) <= &3 / &2 * &n`;;

let THETA_LBOUND_1_2 = `!n. 5 <= n ==> &1 / &2 * &n <= theta(n)`;;

(* ========================================================================= *)
(* Tighten the bounds on weak PNT to get the Bertrand conjecture.            *)
(* ========================================================================= *)

let FLOOR_POS = `!x. &0 <= x ==> &0 <= floor x`;;

let FLOOR_NUM_EXISTS = `!x. &0 <= x ==> ?k. floor x = &k`;;

let FLOOR_DIV_INTERVAL = `!n d k. ~(d = 0)
           ==> ((floor(&n / &d) = &k) =
                  if k = 0 then &n < &d
                  else &n / &(k + 1) < &d /\ &d <= &n / &k)`;;

let FLOOR_DIV_EXISTS = `!n d. ~(d = 0)
         ==> ?k. (floor(&n / &d) = &k) /\
                 d * k <= n /\ n < d * (k + 1)`;;

let FLOOR_HALF_INTERVAL = `!n d. ~(d = 0)
         ==> (floor (&n / &d) - &2 * floor (&(n DIV 2) / &d) =
                if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                then &1 else &0)`;;

let SUM_EXPAND_LEMMA = `!n m k. (m + 2 * k = n)
         ==> (sum (1,n DIV (2 * k + 1))
                  (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                       then mangoldt d else &0) =
              sum (1,n) (\d. --(&1) pow (d + 1) * psi (n DIV d)) -
              sum (1,2 * k)
                  (\d. --(&1) pow (d + 1) * psi (n DIV d)))`;;

let FACT_EXPAND_PSI = `!n. ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2))) =
          sum(1,n) (\d. --(&1) pow (d + 1) * psi(n DIV d))`;;

(* ------------------------------------------------------------------------- *)
(* Show that we can get bounds by cutting off at odd/even points.            *)
(* ------------------------------------------------------------------------- *)

let PSI_MONO = `!m n. m <= n ==> psi(m) <= psi(n)`;;

let PSI_POS = `!n. &0 <= psi(n)`;;

let PSI_EXPANSION_CUTOFF = `!n m p. m <= p
         ==> sum(1,2 * m) (\d. --(&1) pow (d + 1) * psi(n DIV d))
               <= sum(1,2 * p) (\d. --(&1) pow (d + 1) * psi(n DIV d)) /\
             sum(1,2 * p + 1) (\d. --(&1) pow (d + 1) * psi(n DIV d))
               <= sum(1,2 * m + 1) (\d. --(&1) pow (d + 1) * psi(n DIV d))`;;

let FACT_PSI_BOUND_ODD = `!n k. ODD(k)
         ==> ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))
             <= sum(1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))`;;

let FACT_PSI_BOUND_EVEN = `!n k. EVEN(k)
         ==> sum(1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))
             <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))`;;

(* ------------------------------------------------------------------------- *)
(* In particular, we will use these.                                         *)
(* ------------------------------------------------------------------------- *)

let FACT_PSI_BOUND_2_3 = `!n. psi(n) - psi(n DIV 2)
       <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2))) /\
       ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))
       <= psi(n) - psi(n DIV 2) + psi(n DIV 3)`;;

(* ------------------------------------------------------------------------- *)
(* Hence get a good lower bound on psi(n) - psi(n/2).                        *)
(* ------------------------------------------------------------------------- *)

let PSI_DOUBLE_LEMMA = `!n. n >= 1200 ==> &n / &6 <= psi(n) - psi(n DIV 2)`;;

(* ------------------------------------------------------------------------- *)
(* Hence show that theta changes (could get a lower bound like n/10).        *)
(* ------------------------------------------------------------------------- *)

let THETA_DOUBLE_LEMMA = `!n. n >= 1200 ==> theta(n DIV 2) < theta(n)`;;

(* ------------------------------------------------------------------------- *)
(* Hence Bertrand for sufficiently large n.                                  *)
(* ------------------------------------------------------------------------- *)

let BIG_BERTRAND = `!n. n >= 2400 ==> ?p. prime(p) /\ n <= p /\ p <= 2 * n`;;

(* ------------------------------------------------------------------------- *)
(* Landau trick. Should be automatic but ARITH_RULE is a bit slow.           *)
(* (Direct use of ARITH_RULE takes about 3 minutes on my current laptop.)    *)
(* ------------------------------------------------------------------------- *)

let LANDAU_TRICK = `!n. 0 < n /\ n < 2400
       ==> n <= 2 /\ 2 <= 2 * n \/
           n <= 3 /\ 3 <= 2 * n \/
           n <= 5 /\ 5 <= 2 * n \/
           n <= 7 /\ 7 <= 2 * n \/
           n <= 13 /\ 13 <= 2 * n \/
           n <= 23 /\ 23 <= 2 * n \/
           n <= 43 /\ 43 <= 2 * n \/
           n <= 83 /\ 83 <= 2 * n \/
           n <= 163 /\ 163 <= 2 * n \/
           n <= 317 /\ 317 <= 2 * n \/
           n <= 631 /\ 631 <= 2 * n \/
           n <= 1259 /\ 1259 <= 2 * n \/
           n <= 2503 /\ 2503 <= 2 * n`;;

(* ------------------------------------------------------------------------- *)
(* Bertrand for all nonzero n using "Landau trick".                          *)
(* ------------------------------------------------------------------------- *)

let BERTRAND = `!n. ~(n = 0) ==> ?p. prime p /\ n <= p /\ p <= 2 * n`;;

(* ========================================================================= *)
(* Weak form of the Prime Number Theorem.                                    *)
(* ========================================================================= *)

let pii = new_definition
  `pii(n) = sum(1,n) (\p. if prime(p) then &1 else &0)`;;

(* ------------------------------------------------------------------------- *)
(* An optimized rule to give pii(n) for all n <= some N.                     *)
(* ------------------------------------------------------------------------- *)

let PII_LIST =
  let PII_0 = `pii(0) = &0`;;

let PII = `!n. pii(n) = &(CARD {p | p <= n /\ prime(p)})`;;

(* ------------------------------------------------------------------------- *)
(* One bound is a simple consequence of the one for theta.                   *)
(* ------------------------------------------------------------------------- *)

let PII_LBOUND = `!n. 3 <= n ==> &1 / &2 * (&n / ln(&n)) <= pii(n)`;;

(* ------------------------------------------------------------------------- *)
(* First prove the upper bound for the first 50 numbers, to start with.      *)
(* ------------------------------------------------------------------------- *)

let PII_UBOUND_CASES_50 = `!n. n < 50 ==> 3 <= n ==> ln(&n) * pii(n) <= &5 * &n`;;

(* ------------------------------------------------------------------------- *)
(* An extra trivial pair of lemmas.                                          *)
(* ------------------------------------------------------------------------- *)

let THETA_POS = `!n. &0 <= theta n`;;

let PII_MONO = `!m n. m <= n ==> pii(m) <= pii(n)`;;

let PII_POS = `!n. &0 <= pii(n)`;;

(* ------------------------------------------------------------------------- *)
(* The induction principle we can use.                                       *)
(* ------------------------------------------------------------------------- *)

let PII_CHANGE = `!m n. ~(m = 0) ==> ln(&m) * (pii n - pii m) <= &3 / &2 * &n`;;

let PII_ISQRT_INDUCT = `!n. 50 <= n
       ==> ln(&n) * pii(n)
           <= &9 / &4 * (&3 / &2 * &n + ln(&(ISQRT(n))) * pii(ISQRT(n)))`;;

(* ------------------------------------------------------------------------- *)
(* Hence a bound by wellfounded induction.                                   *)
(* ------------------------------------------------------------------------- *)

let PII_UBOUND_5 = `!n. 3 <= n ==> pii(n) <= &5 * (&n / ln(&n))`;;
