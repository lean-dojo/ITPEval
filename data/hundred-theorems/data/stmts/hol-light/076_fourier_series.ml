(* ========================================================================= *)
(* Square integrable functions R->R and basics of Fourier series.            *)
(* ========================================================================= *)

needs "Multivariate/lpspaces.ml";;

(* ------------------------------------------------------------------------- *)
(* Somewhat general lemmas, but perhaps not enough to be installed.          *)
(* ------------------------------------------------------------------------- *)

let SUM_NUMBERS = `!n. sum(0..n) (\r. &r) = (&n * (&n + &1)) / &2`;;

let REAL_INTEGRABLE_REFLECT_AND_ADD = `!f a. f real_integrable_on real_interval[--a,a]
         ==> f real_integrable_on real_interval[&0,a] /\
             (\x. f(--x)) real_integrable_on real_interval[&0,a] /\
             (\x. f x + f(--x)) real_integrable_on real_interval[&0,a]`;;

let REAL_INTEGRAL_REFLECT_AND_ADD = `!f a. f real_integrable_on real_interval[--a,a]
         ==> real_integral (real_interval[--a,a]) f =
             real_integral (real_interval[&0,a])
                           (\x. f x + f(--x))`;;

(* ------------------------------------------------------------------------- *)
(* Square-integrable real->real functions.                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("square_integrable_on",(12,"right"));;

let square_integrable_on = new_definition
 `f square_integrable_on s <=>
     f real_measurable_on s /\ (\x. f(x) pow 2) real_integrable_on s`;;

let SQUARE_INTEGRABLE_IMP_MEASURABLE = `!f s. f square_integrable_on s ==> f real_measurable_on s`;;

let SQUARE_INTEGRABLE_LSPACE = `!f s. f square_integrable_on s <=>
         (lift o f o drop) IN lspace (IMAGE lift s) (&2)`;;

let SQUARE_INTEGRABLE_0 = `!s. (\x. &0) square_integrable_on s`;;

let SQUARE_INTEGRABLE_NEG_EQ = `!f s. (\x. --(f x)) square_integrable_on s <=> f square_integrable_on s`;;

let SQUARE_INTEGRABLE_NEG = `!f s. f square_integrable_on s ==> (\x. --(f x)) square_integrable_on s`;;

let SQUARE_INTEGRABLE_LMUL = `!f s c. f square_integrable_on s ==> (\x. c * f(x)) square_integrable_on s`;;

let SQUARE_INTEGRABLE_RMUL = `!f s c. f square_integrable_on s ==> (\x. f(x) * c) square_integrable_on s`;;

let SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_PRODUCT = `!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) * g(x)) absolutely_real_integrable_on s`;;

let SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT = `!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) * g(x)) real_integrable_on s`;;

let SQUARE_INTEGRABLE_ADD = `!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) + g(x)) square_integrable_on s`;;

let SQUARE_INTEGRABLE_SUB = `!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) - g(x)) square_integrable_on s`;;

let SQUARE_INTEGRABLE_ABS = `!f g s. f square_integrable_on s ==> (\x. abs(f x)) square_integrable_on s`;;

let SQUARE_INTEGRABLE_SUM = `!f s t. FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s)
           ==> (\x. sum t (\i. f i x)) square_integrable_on s`;;

let REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE = `!f a b. f real_continuous_on real_interval[a,b]
           ==> f square_integrable_on real_interval[a,b]`;;

let SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE = `!f s. f square_integrable_on s /\ real_measurable s
         ==> f absolutely_real_integrable_on s`;;

let SQUARE_INTEGRABLE_IMP_INTEGRABLE = `!f s. f square_integrable_on s /\ real_measurable s
         ==> f real_integrable_on s`;;

(* ------------------------------------------------------------------------- *)
(* The norm and inner product in L2.                                         *)
(* ------------------------------------------------------------------------- *)

let l2product = new_definition
 `l2product s f g = real_integral s (\x. f(x) * g(x))`;;

let l2norm = new_definition
 `l2norm s f = sqrt(l2product s f f)`;;

let L2NORM_LNORM = `!f s. f square_integrable_on s
         ==> l2norm s f = lnorm (IMAGE lift s) (&2) (lift o f o drop)`;;

let L2PRODUCT_SYM = `!s f g. l2product s f g = l2product s g f`;;

let L2PRODUCT_POS_LE = `!s f. f square_integrable_on s ==> &0 <= l2product s f f`;;

let L2NORM_POW_2 = `!s f. f square_integrable_on s ==> (l2norm s f) pow 2 = l2product s f f`;;

let L2NORM_POS_LE = `!s f. f square_integrable_on s ==> &0 <= l2norm s f`;;

let L2NORM_LE = `!s f g. f square_integrable_on s /\ g square_integrable_on s
           ==> (l2norm s f <= l2norm s g <=>
                l2product s f f <= l2product s g g)`;;

let L2NORM_EQ = `!s f g. f square_integrable_on s /\ g square_integrable_on s
           ==> (l2norm s f = l2norm s g <=>
                l2product s f f = l2product s g g)`;;

let SCHWARTZ_INEQUALITY_STRONG = `!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2product s (\x. abs(f x)) (\x. abs(g x))
               <= l2norm s f * l2norm s g`;;

let SCHWARTZ_INEQUALITY_ABS = `!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> abs(l2product s f g) <= l2norm s f * l2norm s g`;;

let SCHWARTZ_INEQUALITY = `!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2product s f g <= l2norm s f * l2norm s g`;;

let L2NORM_TRIANGLE = `!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2norm s (\x. f x + g x) <= l2norm s f + l2norm s g`;;

let L2PRODUCT_LADD = `!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s (\x. f x + g x) h =
            l2product s f h + l2product s g h`;;

let L2PRODUCT_RADD = `!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s f (\x. g x + h x) =
            l2product s f g + l2product s f h`;;

let L2PRODUCT_LSUB = `!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s (\x. f x - g x) h =
            l2product s f h - l2product s g h`;;

let L2PRODUCT_RSUB = `!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s f (\x. g x - h x) =
            l2product s f g - l2product s f h`;;

let L2PRODUCT_LZERO = `!s f. l2product s (\x. &0) f = &0`;;

let L2PRODUCT_RZERO = `!s f. l2product s f (\x. &0) = &0`;;

let L2PRODUCT_LSUM = `!s f g t.
        FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s) /\
        g square_integrable_on s
        ==> l2product s (\x. sum t (\i. f i x)) g =
            sum t (\i. l2product s (f i) g)`;;

let L2PRODUCT_RSUM = `!s f g t.
        FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s) /\
        g square_integrable_on s
        ==> l2product s g (\x. sum t (\i. f i x)) =
            sum t (\i. l2product s g (f i))`;;

let L2PRODUCT_LMUL = `!s c f g.
        f square_integrable_on s /\ g square_integrable_on s
        ==> l2product s (\x. c * f x) g = c * l2product s f g`;;

let L2PRODUCT_RMUL = `!s c f g.
        f square_integrable_on s /\ g square_integrable_on s
        ==> l2product s f (\x. c * g x) = c * l2product s f g`;;

let L2NORM_LMUL = `!f s c. f square_integrable_on s
           ==> l2norm s (\x. c * f(x)) = abs(c) * l2norm s f`;;

let L2NORM_RMUL = `!f s c. f square_integrable_on s
           ==> l2norm s (\x. f(x) * c) = l2norm s f * abs(c)`;;

let L2NORM_NEG = `!f s. f square_integrable_on s ==> l2norm s (\x. --(f x)) = l2norm s f`;;

let L2NORM_SUB = `!f g s.  f square_integrable_on s /\ g square_integrable_on s
        ==> l2norm s (\x. f x - g x) = l2norm s (\x. g x - f x)`;;

let L2_SUMMABLE = `!f s t.
     (!i. i IN t ==> (f i) square_integrable_on s) /\
     real_summable t (\i. l2norm s (f i))
     ==> ?g. g square_integrable_on s /\
             ((\n. l2norm s (\x. sum (t INTER (0..n)) (\i. f i x) - g x))
              ---> &0) sequentially`;;

let L2_COMPLETE = `!f s. (!i. f i square_integrable_on s) /\
         (!e. &0 < e ==> ?N. !m n. m >= N /\ n >= N
                                   ==> l2norm s (\x. f m x - f n x) < e)
         ==> ?g. g square_integrable_on s /\
                 ((\n. l2norm s (\x. f n x - g x)) ---> &0) sequentially`;;

let SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS = `!f s e. real_measurable s /\ f square_integrable_on s /\ &0 < e
           ==> ?g. g real_continuous_on (:real) /\
                   g square_integrable_on s /\
                   l2norm s (\x. f x - g x) < e`;;

let SCHWARZ_BOUND = `!f s. real_measurable s /\ f square_integrable_on s
         ==> f absolutely_real_integrable_on s /\
             (real_integral s f) pow 2
             <= real_measure s * real_integral s (\x. f x pow 2)`;;

(* ------------------------------------------------------------------------- *)
(* Orthonormal system of L2 functions and their Fourier coefficients.        *)
(* ------------------------------------------------------------------------- *)

let orthonormal_system = new_definition
 `orthonormal_system s w <=>
        !m n. l2product s (w m) (w n) = if m = n then &1 else &0`;;

let orthonormal_coefficient = new_definition
 `orthonormal_coefficient s w f (n:num) = l2product s (w n) f`;;

let ORTHONORMAL_SYSTEM_L2NORM = `!s w. orthonormal_system s w ==> !i. l2norm s (w i) = &1`;;

let ORTHONORMAL_PARTIAL_SUM_DIFF = `!s w a f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==> l2norm s (\x. f(x) - sum t (\i. a i * w i x)) pow 2 =
            (l2norm s f) pow 2 + sum t (\i. (a i) pow 2) -
            &2 * sum t (\i. a i * orthonormal_coefficient s w f i)`;;

let ORTHONORMAL_OPTIMAL_PARTIAL_SUM = `!s w a f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==>  l2norm s (\x. f(x) -
                           sum t (\i. orthonormal_coefficient s w f i * w i x))
             <= l2norm s (\x. f(x) - sum t (\i. a i * w i x))`;;

let BESSEL_INEQUALITY = `!s w f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==> sum t (\i. (orthonormal_coefficient s w f i) pow 2)
             <= l2norm s f pow 2`;;

let FOURIER_SERIES_SQUARE_SUMMABLE = `!s w f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s
        ==> real_summable t (\i. (orthonormal_coefficient s w f i) pow 2)`;;

let ORTHONORMAL_FOURIER_PARTIAL_SUM_DIFF_SQUARED = `!s w a f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s /\ FINITE t
    ==> l2norm s (\x. f x -
                      sum t (\i. orthonormal_coefficient s w f i * w i x))
        pow 2 =
        l2norm s f pow 2 - sum t (\i. orthonormal_coefficient s w f i pow 2)`;;

let FOURIER_SERIES_L2_SUMMABLE = `!s w f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s
    ==> ?g. g square_integrable_on s /\
            ((\n. l2norm s
                    (\x. sum (t INTER (0..n))
                             (\i. orthonormal_coefficient s w f i * w i x) -
                         g(x))) ---> &0) sequentially`;;

let FOURIER_SERIES_L2_SUMMABLE_STRONG = `!s w f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s
    ==> ?g. g square_integrable_on s /\
            (!i. i IN t
                 ==> orthonormal_coefficient s w (\x. f x - g x) i = &0) /\
            ((\n. l2norm s
                   (\x. sum (t INTER (0..n))
                            (\i. orthonormal_coefficient s w f i * w i x) -
                        g(x))) ---> &0) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Actual trigonometric orthogonality relations.                             *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRABLE_ON_INTERVAL_TAC =
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  GEN_TAC THEN DISCH_TAC THEN REAL_DIFFERENTIABLE_TAC;;

let HAS_REAL_INTEGRAL_SIN_NX = `!n. ((\x. sin(&n * x)) has_real_integral &0) (real_interval[--pi,pi])`;;

let REAL_INTEGRABLE_SIN_CX = `!c. (\x. sin(c * x)) real_integrable_on real_interval[--pi,pi]`;;

let REAL_INTEGRAL_SIN_NX = `!n. real_integral (real_interval[--pi,pi]) (\x. sin(&n * x)) = &0`;;

let HAS_REAL_INTEGRAL_COS_NX = `!n. ((\x. cos(&n * x)) has_real_integral (if n = 0 then &2 * pi else &0))
       (real_interval[--pi,pi])`;;

let REAL_INTEGRABLE_COS_CX = `!c. (\x. cos(c * x)) real_integrable_on real_interval[--pi,pi]`;;

let REAL_INTEGRAL_COS_NX = `!n. real_integral (real_interval[--pi,pi]) (\x. cos(&n * x)) =
       if n = 0 then &2 * pi else &0`;;

let REAL_INTEGRAL_SIN_AND_COS = `!m n. real_integral (real_interval[--pi,pi])
           (\x. cos(&m * x) * cos(&n * x)) =
                (if m = n then if n = 0 then &2 * pi else pi else &0) /\
         real_integral (real_interval[--pi,pi])
           (\x. cos(&m * x) * sin(&n * x)) = &0 /\
         real_integral (real_interval[--pi,pi])
           (\x. sin(&m * x) * cos(&n * x)) = &0 /\
         real_integral (real_interval[--pi,pi])
           (\x. sin(&m * x) * sin(&n * x)) =
              (if m = n /\ ~(n = 0) then pi else &0)`;;

let REAL_INTEGRABLE_SIN_AND_COS = `!m n a b.
      (\x. cos(&m * x) * cos(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. cos(&m * x) * sin(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. sin(&m * x) * cos(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. sin(&m * x) * sin(&n * x)) real_integrable_on real_interval[a,b]`;;

let trigonometric_set_def = new_definition
 `trigonometric_set n =
    if n = 0 then \x. &1 / sqrt(&2 * pi)
    else if ODD n then \x. sin(&(n DIV 2 + 1) * x) / sqrt(pi)
    else \x. cos(&(n DIV 2) * x) / sqrt(pi)`;;

let trigonometric_set = `trigonometric_set 0 = (\x. cos(&0 * x) / sqrt(&2 * pi)) /\
   trigonometric_set (2 * n + 1) = (\x. sin(&(n + 1) * x) / sqrt(pi)) /\
   trigonometric_set (2 * n + 2) = (\x. cos(&(n + 1) * x) / sqrt(pi))`;;

let TRIGONOMETRIC_SET_EVEN = `!k. trigonometric_set(2 * k) =
        if k = 0 then \x. &1 / sqrt(&2 * pi)
        else \x. cos(&k * x) / sqrt pi`;;

let ODD_EVEN_INDUCT_LEMMA = `(!n:num. P 0) /\ (!n. P(2 * n + 1)) /\ (!n. P(2 * n + 2)) ==> !n. P n`;;

let ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET = `orthonormal_system (real_interval[--pi,pi]) trigonometric_set`;;

let SQUARE_INTEGRABLE_TRIGONOMETRIC_SET = `!i. (trigonometric_set i) square_integrable_on real_interval[--pi,pi]`;;

(* ------------------------------------------------------------------------- *)
(* Weierstrass for trigonometric polynomials.                                *)
(* ------------------------------------------------------------------------- *)

let WEIERSTRASS_TRIG_POLYNOMIAL = `!f e. f real_continuous_on real_interval[--pi,pi] /\
         f(--pi) = f pi /\ &0 < e
         ==> ?n a b.
                !x. x IN real_interval[--pi,pi]
                    ==> abs(f x - sum(0..n) (\k. a k * sin(&k * x) +
                                                 b k * cos(&k * x))) < e`;;

(* ------------------------------------------------------------------------- *)
(* A bit of extra hacking round so that the ends of a function are OK.       *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRAL_TWEAK_ENDS = `!a b d e.
        a < b /\ &0 < e
        ==> ?f. f real_continuous_on real_interval[a,b] /\
                f(a) = d /\ f(b) = &0 /\
                l2norm (real_interval[a,b]) f < e`;;

let SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS = `!f a b e.
        f square_integrable_on real_interval[a,b] /\ a < b /\ &0 < e
        ==> ?g. g real_continuous_on real_interval[a,b] /\
                g b = g a /\
                g square_integrable_on real_interval[a,b] /\
                l2norm (real_interval[a,b]) (\x. f x - g x) < e`;;

(* ------------------------------------------------------------------------- *)
(* Hence the main approximation result.                                      *)
(* ------------------------------------------------------------------------- *)

let WEIERSTRASS_L2_TRIG_POLYNOMIAL = `!f e. f square_integrable_on real_interval[--pi,pi] /\ &0 < e
         ==> ?n a b.
                l2norm (real_interval[--pi,pi])
                       (\x. f x - sum(0..n) (\k. a k * sin(&k * x) +
                                                 b k * cos(&k * x))) < e`;;

let WEIERSTRASS_L2_TRIGONOMETRIC_SET = `!f e. f square_integrable_on real_interval[--pi,pi] /\ &0 < e
         ==> ?n a.
                l2norm (real_interval[--pi,pi])
                       (\x. f x -
                            sum(0..n) (\k. a k * trigonometric_set k x))
                < e`;;

(* ------------------------------------------------------------------------- *)
(* Convergence w.r.t. L2 norm of trigonometric Fourier series.               *)
(* ------------------------------------------------------------------------- *)

let fourier_coefficient = new_definition
 `fourier_coefficient =
    orthonormal_coefficient (real_interval[--pi,pi]) trigonometric_set`;;

let FOURIER_SERIES_L2 = `!f. f square_integrable_on real_interval[--pi,pi]
       ==> ((\n. l2norm (real_interval[--pi,pi])
                        (\x. f(x) - sum(0..n) (\i. fourier_coefficient f i *
                                                   trigonometric_set i x)))
            ---> &0) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Fourier coefficients go to 0 (weak form of Riemann-Lebesgue).             *)
(* ------------------------------------------------------------------------- *)

let TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE = `!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. trigonometric_set n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`;;

let TRIGONOMETRIC_SET_MUL_INTEGRABLE = `!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. trigonometric_set n x * f x)
             real_integrable_on real_interval[--pi,pi]`;;

let ABSOLUTELY_INTEGRABLE_SIN_PRODUCT,ABSOLUTELY_INTEGRABLE_COS_PRODUCT =
 (CONJ_PAIR o prove)
 (`(!f k. f absolutely_real_integrable_on real_interval[--pi,pi]
          ==> (\x. sin(k * x) * f x) absolutely_real_integrable_on
              real_interval[--pi,pi]) /\
   (!f k. f absolutely_real_integrable_on real_interval[--pi,pi]
          ==> (\x. cos(k * x) * f x) absolutely_real_integrable_on
              real_interval[--pi,pi])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  (ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
     EXISTS_TAC `(:real)` THEN
     REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
     MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
     MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
     REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
     SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
     REWRITE_TAC[trigonometric_set; real_div] THEN
     REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
     REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
     SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
     REWRITE_TAC[trigonometric_set; COS_BOUND; SIN_BOUND]]));;

let FOURIER_PRODUCTS_INTEGRABLE_STRONG = `!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> f real_integrable_on real_interval[--pi,pi] /\
           (!k. (\x. cos(k * x) * f x) real_integrable_on
                real_interval[--pi,pi]) /\
           (!k. (\x. sin(k * x) * f x) real_integrable_on
                real_interval[--pi,pi])`;;

let FOURIER_PRODUCTS_INTEGRABLE = `!f. f square_integrable_on real_interval[--pi,pi]
       ==> f real_integrable_on real_interval[--pi,pi] /\
           (!k. (\x. cos(k * x) * f x) real_integrable_on
                real_interval[--pi,pi]) /\
           (!k. (\x. sin(k * x) * f x) real_integrable_on
                real_interval[--pi,pi])`;;

let ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS = `!f s e. real_measurable s /\ f absolutely_real_integrable_on s /\ &0 < e
           ==> ?g. g real_continuous_on (:real) /\
                   g absolutely_real_integrable_on s /\
                   real_integral s (\x. abs(f x - g x)) < e`;;

let RIEMANN_LEBESGUE_SQUARE_INTEGRABLE = `!s w f.
        orthonormal_system s w /\
        (!i. w i square_integrable_on s) /\
        f square_integrable_on s
        ==> (orthonormal_coefficient s w f ---> &0) sequentially`;;

let RIEMANN_LEBESGUE = `!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> (fourier_coefficient f ---> &0) sequentially`;;

let RIEMANN_LEBESGUE_SIN = `!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                                 (\x. sin(&n * x) * f x)) ---> &0)
              sequentially`;;

let RIEMANN_LEBESGUE_COS = `!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                                 (\x. cos(&n * x) * f x)) ---> &0)
              sequentially`;;

let RIEMANN_LEBESGUE_SIN_HALF = `!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                               (\x. sin((&n + &1 / &2) * x) * f x)) ---> &0)
              sequentially`;;

let FOURIER_SUM_LIMIT_PAIR = `!f n t l.
        f absolutely_real_integrable_on real_interval [--pi,pi]
        ==> (((\n. sum(0..2*n) (\k. fourier_coefficient f k *
                                    trigonometric_set k t)) ---> l)
             sequentially <=>
             ((\n. sum(0..n) (\k. fourier_coefficient f k *
                                  trigonometric_set k t)) ---> l)
             sequentially)`;;

(* ------------------------------------------------------------------------- *)
(* Express Fourier sum in terms of the special expansion at the origin.      *)
(* ------------------------------------------------------------------------- *)

let FOURIER_SUM_0 = `!f n.
     sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
     sum (0..n DIV 2)
         (\k. fourier_coefficient f (2 * k) * trigonometric_set (2 * k) (&0))`;;

let FOURIER_SUM_0_EXPLICIT = `!f n.
     sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
     (fourier_coefficient f 0 / sqrt(&2) +
      sum (1..n DIV 2) (\k. fourier_coefficient f (2 * k))) / sqrt pi`;;

let FOURIER_SUM_0_INTEGRALS = `!f n.
      f absolutely_real_integrable_on real_interval[--pi,pi]
      ==> sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
          (real_integral(real_interval[--pi,pi]) f / &2 +
           sum(1..n DIV 2) (\k. real_integral (real_interval[--pi,pi])
                                              (\x. cos(&k * x) * f x))) / pi`;;

let FOURIER_SUM_0_INTEGRAL = `!f n.
      f absolutely_real_integrable_on real_interval[--pi,pi]
      ==> sum(0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
          real_integral(real_interval[--pi,pi])
           (\x. (&1 / &2 + sum(1..n DIV 2) (\k. cos(&k * x))) * f x) / pi`;;

(* ------------------------------------------------------------------------- *)
(* How Fourier coefficients behave under addition etc.                       *)
(* ------------------------------------------------------------------------- *)

let FOURIER_COEFFICIENT_ADD = `!f g i. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           g absolutely_real_integrable_on real_interval[--pi,pi]
           ==> fourier_coefficient (\x. f x + g x) i =
                fourier_coefficient f i + fourier_coefficient g i`;;

let FOURIER_COEFFICIENT_SUB = `!f g i. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           g absolutely_real_integrable_on real_interval[--pi,pi]
           ==> fourier_coefficient (\x. f x - g x) i =
                fourier_coefficient f i - fourier_coefficient g i`;;

let FOURIER_COEFFICIENT_CONST = `!c i. fourier_coefficient (\x. c) i =
         if i = 0 then c * sqrt(&2 * pi) else &0`;;

(* ------------------------------------------------------------------------- *)
(* Shifting the origin for integration of periodic functions.                *)
(* ------------------------------------------------------------------------- *)

let REAL_PERIODIC_INTEGER_MULTIPLE = `!f:real->real a.
        (!x. f(x + a) = f x) <=> (!x n. integer n ==> f(x + n * a) = f x)`;;

let HAS_REAL_INTEGRAL_OFFSET = `!f i a b c. (f has_real_integral i) (real_interval[a,b])
                ==> ((\x. f(x + c)) has_real_integral i)
                    (real_interval[a - c,b - c])`;;

let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA = `!f i a b c.
        (!x. f(x + (b - a)) = f(x)) /\
        (f has_real_integral i) (real_interval[a,a+c])
        ==> (f has_real_integral i) (real_interval[b,b+c])`;;

let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS = `!f i a b c.
        (!x. f(x + (b - a)) = f x) /\ &0 <= c /\ a + c <= b /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i)
             (real_interval[a,b])`;;

let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK = `!f i a b c.
        (!x. f(x + (b - a)) = f x) /\ abs(c) <= b - a /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i)
             (real_interval[a,b])`;;

let HAS_REAL_INTEGRAL_PERIODIC_OFFSET = `!f i a b c.
        (!x. f(x + (b - a)) = f x) /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i) (real_interval[a,b])`;;

let REAL_INTEGRABLE_PERIODIC_OFFSET = `!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f real_integrable_on real_interval[a,b]
        ==> (\x. f(x + c)) real_integrable_on real_interval[a,b]`;;

let ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET = `!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f absolutely_real_integrable_on real_interval[a,b]
        ==> (\x. f(x + c)) absolutely_real_integrable_on real_interval[a,b]`;;

let REAL_INTEGRAL_PERIODIC_OFFSET = `!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f real_integrable_on real_interval[a,b]
        ==> real_integral (real_interval[a,b]) (\x. f(x + c)) =
            real_integral (real_interval[a,b]) f`;;

let FOURIER_OFFSET_TERM = `!f n t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           (!x. f(x + &2 * pi) = f x)
           ==> fourier_coefficient (\x. f(x + t)) (2 * n + 2) *
               trigonometric_set (2 * n + 2) (&0) =
               fourier_coefficient f (2 * n + 1) *
               trigonometric_set (2 * n + 1) t +
               fourier_coefficient f (2 * n + 2) *
               trigonometric_set (2 * n + 2) t`;;

let FOURIER_SUM_OFFSET = `!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k *
                             trigonometric_set k t) =
            sum(0..2*n) (\k. fourier_coefficient (\x. f (x + t)) k *
                             trigonometric_set k (&0))`;;

let FOURIER_SUM_OFFSET_UNPAIRED = `!f n t.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k *
                             trigonometric_set k t) =
            sum(0..n) (\k. fourier_coefficient (\x. f (x + t)) (2 * k) *
                           trigonometric_set (2 * k) (&0))`;;

(* ------------------------------------------------------------------------- *)
(* Express partial sums using Dirichlet kernel.                              *)
(* ------------------------------------------------------------------------- *)

let dirichlet_kernel = new_definition
 `dirichlet_kernel n x =
        if x = &0 then &n + &1 / &2
        else sin((&n + &1 / &2) * x) / (&2 * sin(x / &2))`;;

let DIRICHLET_KERNEL_0 = `!x. abs(x) < &2 * pi ==> dirichlet_kernel 0 x = &1 / &2`;;

let DIRICHLET_KERNEL_NEG = `!n x. dirichlet_kernel n (--x) = dirichlet_kernel n x`;;

let DIRICHLET_KERNEL_CONTINUOUS_STRONG = `!n. (dirichlet_kernel n) real_continuous_on
       real_interval(--(&2 * pi),&2 * pi)`;;

let DIRICHLET_KERNEL_CONTINUOUS = `!n. (dirichlet_kernel n) real_continuous_on real_interval[--pi,pi]`;;

let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL = `!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. dirichlet_kernel n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`;;

let COSINE_SUM_LEMMA = `!n x. (&1 / &2 + sum(1..n) (\k. cos(&k * x))) * sin(x / &2) =
         sin((&n + &1 / &2) * x) / &2`;;

let DIRICHLET_KERNEL_COSINE_SUM = `!n x. ~(x = &0) /\ abs(x) < &2 * pi
         ==> dirichlet_kernel n x = &1 / &2 + sum(1..n) (\k. cos(&k * x))`;;

let HAS_REAL_INTEGRAL_DIRICHLET_KERNEL = `!n. (dirichlet_kernel n has_real_integral pi) (real_interval[--pi,pi])`;;

let HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF = `!n. (dirichlet_kernel n has_real_integral (pi / &2))
       (real_interval[&0,pi])`;;

let FOURIER_SUM_OFFSET_DIRICHLET_KERNEL = `!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k * trigonometric_set k t) =
            real_integral (real_interval[--pi,pi])
                          (\x. dirichlet_kernel n x * f(x + t)) / pi`;;

let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL = `!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x + t)))
             ---> pi * l) sequentially)`;;

(* ------------------------------------------------------------------------- *)
(* A directly deduced sufficient condition for convergence at a point.       *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_FOURIER_CONVERGENCE_PERIODIC = `!f t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (\x. (f(x + t) - f(t)) / sin(x / &2))
        absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f(t)) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* A more natural sufficient Hoelder condition at a point.                   *)
(* ------------------------------------------------------------------------- *)

let REAL_SIN_X2_ZEROS = `{x | sin(x / &2) = &0} = IMAGE (\n. &2 * pi * n) integer`;;

let HOELDER_FOURIER_CONVERGENCE_PERIODIC = `!f d M a t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\
        &0 < d /\ &0 < a /\
        (!x. abs(x - t) < d ==> abs(f x - f t) <= M * abs(x - t) rpow a)
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> f t) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* In particular, a Lipschitz condition at the point.                        *)
(* ------------------------------------------------------------------------- *)

let LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC = `!f d M t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\
        &0 < d /\ (!x. abs(x - t) < d ==> abs(f x - f t) <= M * abs(x - t))
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> f t) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* In particular, if left and right derivatives both exist.                  *)
(* ------------------------------------------------------------------------- *)

let BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC = `!f t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f(x)) /\
         f real_differentiable (atreal t within {x | t < x}) /\
         f real_differentiable (atreal t within {x | x < t})
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f t) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* And in particular at points where the function is differentiable.         *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC = `!f t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f(x)) /\
         f real_differentiable (atreal t)
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f t) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Use reflection to halve the region of integration.                        *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED = `!f n c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x))
        ==> (\x. dirichlet_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. dirichlet_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. dirichlet_kernel n x * c)
            absolutely_real_integrable_on real_interval[--pi,pi]`;;

let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART = `!f n d c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ d <= pi
        ==> (\x. dirichlet_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * c)
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * (f(t + x) + f(t - x)))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * ((f(t + x) + f(t - x)) - c))
            absolutely_real_integrable_on real_interval[&0,d]`;;

let FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF = `!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k * trigonometric_set k t) -
            l =
            real_integral (real_interval[&0,pi])
                          (\x. dirichlet_kernel n x *
                               ((f(t + x) + f(t - x)) - &2 * l)) / pi`;;

let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF = `!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,pi])
                                (\x. dirichlet_kernel n x *
                                     ((f(t + x) + f(t - x)) - &2 * l)))
             ---> &0) sequentially)`;;

(* ------------------------------------------------------------------------- *)
(* Localization principle: convergence only depends on values "nearby".      *)
(* ------------------------------------------------------------------------- *)

let RIEMANN_LOCALIZATION_INTEGRAL = `!d f g.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        g absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ (!x. abs(x) < d ==> f x = g x)
        ==> ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x)) -
                  real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * g(x)))
             ---> &0) sequentially`;;

let RIEMANN_LOCALIZATION_INTEGRAL_RANGE = `!d f.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ d <= pi
        ==> ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x)) -
                  real_integral (real_interval[--d,d])
                                (\x. dirichlet_kernel n x * f(x)))
             ---> &0) sequentially`;;

let RIEMANN_LOCALIZATION = `!t d c f g.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        g absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ (!x. g(x + &2 * pi) = g(x)) /\
        &0 < d /\ (!x. abs(x - t) < d ==> f x = g x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> c) sequentially <=>
             ((\n. sum (0..n)
                       (\k. fourier_coefficient g k * trigonometric_set k t))
              ---> c) sequentially)`;;

(* ------------------------------------------------------------------------- *)
(* Localize the earlier integral.                                            *)
(* ------------------------------------------------------------------------- *)

let RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF = `!d f.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ d <= pi
        ==> ((\n. real_integral (real_interval[&0,pi])
                                (\x. dirichlet_kernel n x * (f(x) + f(--x))) -
                  real_integral (real_interval[&0,d])
                                (\x. dirichlet_kernel n x * (f(x) + f(--x))))
             ---> &0) sequentially`;;

let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART = `!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\ &0 < d /\ d <= pi
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,d])
                                (\x. dirichlet_kernel n x *
                                     ((f(t + x) + f(t - x)) - &2 * l)))
             ---> &0) sequentially)`;;

(* ------------------------------------------------------------------------- *)
(* Make a harmless simplifying tweak to the Dirichlet kernel.                *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND = `!f n s. real_integral s (\x. dirichlet_kernel n x * f x) =
           real_integral s (\x. sin((&n + &1 / &2) * x) / (&2 * sin(x / &2)) *
                                f x)`;;

let REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND = `!f n s. (\x. dirichlet_kernel n x * f x) real_integrable_on s <=>
           (\x. sin((&n + &1 / &2) * x) / (&2 * sin(x / &2)) * f x)
           real_integrable_on s`;;

let FOURIER_SUM_LIMIT_SINE_PART = `!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\ &0 < d /\ d <= pi
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,d])
                                (\x. sin((&n + &1 / &2) * x) *
                                     ((f(t + x) + f(t - x)) - &2 * l) / x))
             ---> &0) sequentially)`;;

(* ------------------------------------------------------------------------- *)
(* Dini's test.                                                              *)
(* ------------------------------------------------------------------------- *)

let FOURIER_DINI_TEST = `!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\
        &0 < d /\
        (\x. abs((f(t + x) + f(t - x)) - &2 * l) / x)
        real_integrable_on real_interval[&0,d]
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> l) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Convergence for functions of bounded variation.                           *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRAL_SIN_OVER_X_BOUND = `!a b c.
       &0 <= a /\ &0 < c
       ==> (\x. sin(c * x) / x) real_integrable_on real_interval[a,b] /\
           abs(real_integral (real_interval[a,b]) (\x. sin(c * x) / x)) <= &4`;;

let FOURIER_JORDAN_BOUNDED_VARIATION = `!f x d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f x) /\
        &0 < d /\
        f has_bounded_real_variation_on real_interval[x - d,x + d]
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k x))
             ---> ((reallim (atreal x within {l | l <= x}) f +
                    reallim (atreal x within {r | r >= x}) f) / &2))
            sequentially`;;

let FOURIER_JORDAN_BOUNDED_VARIATION_SIMPLE = `!f x. f has_bounded_real_variation_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f x)
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k x))
              ---> ((reallim (atreal x within {l | l <= x}) f +
                     reallim (atreal x within {r | r >= x}) f) / &2))
             sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Cesaro summability of Fourier series using Fejer kernel.                  *)
(* ------------------------------------------------------------------------- *)

let fejer_kernel = new_definition
  `fejer_kernel n x = if n = 0 then &0
                      else sum(0..n-1) (\r. dirichlet_kernel r x) / &n`;;

let FEJER_KERNEL = `fejer_kernel n x =
        if n = 0 then &0
        else if x = &0 then &n / &2
        else sin(&n / &2 * x) pow 2 / (&2 * &n * sin(x / &2) pow 2)`;;

let FEJER_KERNEL_CONTINUOUS_STRONG = `!n. (fejer_kernel n) real_continuous_on
       real_interval(--(&2 * pi),&2 * pi)`;;

let FEJER_KERNEL_CONTINUOUS = `!n. (fejer_kernel n) real_continuous_on real_interval[--pi,pi]`;;

let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL = `!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. fejer_kernel n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`;;

let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED = `!f n c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x))
        ==> (\x. fejer_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. fejer_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. fejer_kernel n x * c)
            absolutely_real_integrable_on real_interval[--pi,pi]`;;

let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART = `!f n d c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ d <= pi
        ==> (\x. fejer_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * c)
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * (f(t + x) + f(t - x)))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * ((f(t + x) + f(t - x)) - c))
            absolutely_real_integrable_on real_interval[&0,d]`;;

let FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF = `!f n t.
     f absolutely_real_integrable_on real_interval[--pi,pi] /\
     (!x. f (x + &2 * pi) = f x) /\
     0 < n
     ==> sum(0..n-1) (\r. sum (0..2*r)
                              (\k. fourier_coefficient f k *
                                   trigonometric_set k t)) / &n - l =
         real_integral (real_interval[&0,pi])
                       (\x. fejer_kernel n x *
                            ((f(t + x) + f(t - x)) - &2 * l)) / pi`;;

let FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF = `!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum(0..n-1) (\r. sum (0..2*r)
                                        (\k. fourier_coefficient f k *
                                             trigonometric_set k t)) / &n)
               ---> l) sequentially <=>
             ((\n. real_integral (real_interval[&0,pi])
                                 (\x. fejer_kernel n x *
                                      ((f(t + x) + f(t - x)) - &2 * l)))
              ---> &0) sequentially)`;;

let HAS_REAL_INTEGRAL_FEJER_KERNEL = `!n. (fejer_kernel n has_real_integral (if n = 0 then &0 else pi))
       (real_interval[--pi,pi])`;;

let HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF = `!n. (fejer_kernel n has_real_integral (if n = 0 then &0 else pi / &2))
       (real_interval[&0,pi])`;;

let FEJER_KERNEL_POS_LE = `!n x. &0 <= fejer_kernel n x`;;

let FOURIER_FEJER_CESARO_SUMMABLE = `!f x l r.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f x) /\
        (f ---> l) (atreal x within {x' | x' <= x}) /\
        (f ---> r) (atreal x within {x' | x' >= x})
        ==> ((\n. sum(0..n-1) (\m. sum (0..2*m)
                                       (\k. fourier_coefficient f k *
                                            trigonometric_set k x)) / &n)
             ---> (l + r) / &2)
            sequentially`;;

let FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE = `!f x l r.
        f real_continuous_on (:real) /\ (!x. f(x + &2 * pi) = f x)
        ==> ((\n. sum(0..n-1) (\m. sum (0..2*m)
                                       (\k. fourier_coefficient f k *
                                            trigonometric_set k x)) / &n)
             ---> f(x))
            sequentially`;;
