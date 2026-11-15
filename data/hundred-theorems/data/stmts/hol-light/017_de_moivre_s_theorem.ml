(* ========================================================================= *)
(* Complex transcendentals and their real counterparts.                      *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Multivariate/measure.ml";;
needs "Multivariate/canal.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The complex exponential function.                                         *)
(* ------------------------------------------------------------------------- *)

let cexp = new_definition
 `cexp z = infsum (from 0) (\n. z pow n / Cx(&(FACT n)))`;;

let CEXP_0 = `cexp(Cx(&0)) = Cx(&1)`;;

let CEXP_CONVERGES_UNIFORMLY_CAUCHY = `!R e. &0 < e /\ &0 < R
         ==> ?N. !m n z. m >= N /\ norm(z) <= R
                         ==> norm(vsum(m..n) (\i. z pow i / Cx(&(FACT i))))
                                     < e`;;

let CEXP_CONVERGES = `!z. ((\n. z pow n / Cx(&(FACT n))) sums cexp(z)) (from 0)`;;

let CEXP_CONVERGES_UNIQUE = `!w z. ((\n. z pow n / Cx(&(FACT n))) sums w) (from 0) <=> w = cexp(z)`;;

let CEXP_CONVERGES_UNIFORMLY = `!R e. &0 < R /\ &0 < e
         ==> ?N. !n z. n >= N /\ norm(z) < R
                       ==> norm(vsum(0..n) (\i. z pow i / Cx(&(FACT i))) -
                                cexp(z)) <= e`;;

let HAS_COMPLEX_DERIVATIVE_CEXP = `!z. (cexp has_complex_derivative cexp(z)) (at z)`;;

let COMPLEX_DIFFERENTIABLE_AT_CEXP = `!z. cexp complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_CEXP = `!s z. cexp complex_differentiable (at z within s)`;;

let CONTINUOUS_AT_CEXP = `!z. cexp continuous at z`;;

let CONTINUOUS_WITHIN_CEXP = `!s z. cexp continuous (at z within s)`;;

let CONTINUOUS_ON_CEXP = `!s. cexp continuous_on s`;;

let HOLOMORPHIC_ON_CEXP = `!s. cexp holomorphic_on s`;;

(* ------------------------------------------------------------------------- *)
(* Add it to the database.                                                   *)
(* ------------------------------------------------------------------------- *)

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
             HAS_COMPLEX_DERIVATIVE_CEXP)));;

(* ------------------------------------------------------------------------- *)
(* Hence the main results.                                                   *)
(* ------------------------------------------------------------------------- *)

let CEXP_ADD_MUL = `!w z. cexp(w + z) * cexp(--z) = cexp(w)`;;

let CEXP_NEG_RMUL = `!z. cexp(z) * cexp(--z) = Cx(&1)`;;

let CEXP_NEG_LMUL = `!z. cexp(--z) * cexp(z) = Cx(&1)`;;

let CEXP_NEG = `!z. cexp(--z) = inv(cexp z)`;;

let CEXP_ADD = `!w z. cexp(w + z) = cexp(w) * cexp(z)`;;

let CEXP_SUB = `!w z. cexp(w - z) = cexp(w) / cexp(z)`;;

let CEXP_NZ = `!z. ~(cexp(z) = Cx(&0))`;;

let CEXP_N = `!n x. cexp(Cx(&n) * x) = cexp(x) pow n`;;

let CEXP_VSUM = `!f s. FINITE s ==> cexp(vsum s f) = cproduct s (\x. cexp(f x))`;;

let LIM_CEXP_MINUS_1 = `((\z. (cexp(z) - Cx(&1)) / z) --> Cx(&1)) (at (Cx(&0)))`;;

(* ------------------------------------------------------------------------- *)
(* Crude bounds on complex exponential function, usable to get tighter ones. *)
(* ------------------------------------------------------------------------- *)

let CEXP_BOUND_BLEMMA = `!B. (!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= B)
       ==> !z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &1 + B / &2`;;

let CEXP_BOUND_HALF = `!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &2`;;

let CEXP_BOUND_LEMMA = `!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &1 + &2 * norm(z)`;;

(* ------------------------------------------------------------------------- *)
(* Complex trig functions.                                                   *)
(* ------------------------------------------------------------------------- *)

let ccos = new_definition
  `ccos z = (cexp(ii * z) + cexp(--ii * z)) / Cx(&2)`;;

let csin = new_definition
  `csin z = (cexp(ii * z) - cexp(--ii * z)) / (Cx(&2) * ii)`;;

let CSIN_0 = `csin(Cx(&0)) = Cx(&0)`;;

let CCOS_0 = `ccos(Cx(&0)) = Cx(&1)`;;

let CSIN_CIRCLE = `!z. csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)`;;

let CSIN_ADD = `!w z. csin(w + z) = csin(w) * ccos(z) + ccos(w) * csin(z)`;;

let CCOS_ADD = `!w z. ccos(w + z) = ccos(w) * ccos(z) - csin(w) * csin(z)`;;

let CSIN_NEG = `!z. csin(--z) = --(csin(z))`;;

let CCOS_NEG = `!z. ccos(--z) = ccos(z)`;;

let CSIN_DOUBLE = `!z. csin(Cx(&2) * z) = Cx(&2) * csin(z) * ccos(z)`;;

let CCOS_DOUBLE = `!z. ccos(Cx(&2) * z) = (ccos(z) pow 2) - (csin(z) pow 2)`;;

let CSIN_SUB = `!w z. csin(w - z) = csin(w) * ccos(z) - ccos(w) * csin(z)`;;

let CCOS_SUB = `!w z. ccos(w - z) = ccos(w) * ccos(z) + csin(w) * csin(z)`;;

let COMPLEX_MUL_CSIN_CSIN = `!w z. csin(w) * csin(z) = (ccos(w - z) - ccos(w + z)) / Cx(&2)`;;

let COMPLEX_MUL_CSIN_CCOS = `!w z. csin(w) * ccos(z) = (csin(w + z) + csin(w - z)) / Cx(&2)`;;

let COMPLEX_MUL_CCOS_CSIN = `!w z. ccos(w) * csin(z) = (csin(w + z) - csin(w - z)) / Cx(&2)`;;

let COMPLEX_MUL_CCOS_CCOS = `!w z. ccos(w) * ccos(z) = (ccos(w - z) + ccos(w + z)) / Cx(&2)`;;

let COMPLEX_ADD_CSIN = `!w z. csin(w) + csin(z) =
         Cx(&2) * csin((w + z) / Cx(&2)) * ccos((w - z) / Cx(&2))`;;

let COMPLEX_SUB_CSIN = `!w z. csin(w) - csin(z) =
         Cx(&2) * csin((w - z) / Cx(&2)) * ccos((w + z) / Cx(&2))`;;

let COMPLEX_ADD_CCOS = `!w z. ccos(w) + ccos(z) =
         Cx(&2) * ccos((w + z) / Cx(&2)) * ccos((w - z) / Cx(&2))`;;

let COMPLEX_SUB_CCOS = `!w z. ccos(w) - ccos(z) =
         Cx(&2) * csin((w + z) / Cx(&2)) * csin((z - w) / Cx(&2))`;;

let CCOS_DOUBLE_CCOS = `!z. ccos(Cx(&2) * z) = Cx(&2) * ccos z pow 2 - Cx(&1)`;;

let CCOS_DOUBLE_CSIN = `!z. ccos(Cx(&2) * z) = Cx(&1) - Cx(&2) * csin z pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Euler and de Moivre formulas.                                             *)
(* ------------------------------------------------------------------------- *)

let CEXP_EULER = `!z. cexp(ii * z) = ccos(z) + ii * csin(z)`;;

let DEMOIVRE = `!z n. (ccos z + ii * csin z) pow n =
         ccos(Cx(&n) * z) + ii * csin(Cx(&n) * z)`;;

(* ------------------------------------------------------------------------- *)
(* Real exponential function. Same names as old Library/transc.ml.           *)
(* ------------------------------------------------------------------------- *)

let exp = new_definition `exp(x) = Re(cexp(Cx x))`;;

let CNJ_CEXP = `!z. cnj(cexp z) = cexp(cnj z)`;;

let REAL_EXP = `!z. real z ==> real(cexp z)`;;

let CX_EXP = `!x. Cx(exp x) = cexp(Cx x)`;;

let REAL_EXP_ADD = `!x y. exp(x + y) = exp(x) * exp(y)`;;

let REAL_EXP_0 = `exp(&0) = &1`;;

let REAL_EXP_ADD_MUL = `!x y. exp(x + y) * exp(--x) = exp(y)`;;

let REAL_EXP_NEG_MUL = `!x. exp(x) * exp(--x) = &1`;;

let REAL_EXP_NEG_MUL2 = `!x. exp(--x) * exp(x) = &1`;;

let REAL_EXP_NEG = `!x. exp(--x) = inv(exp(x))`;;

let REAL_EXP_N = `!n x. exp(&n * x) = exp(x) pow n`;;

let REAL_EXP_SUB = `!x y. exp(x - y) = exp(x) / exp(y)`;;

let REAL_EXP_NZ = `!x. ~(exp(x) = &0)`;;

let REAL_EXP_POS_LE = `!x. &0 <= exp(x)`;;

let REAL_EXP_POS_LT = `!x. &0 < exp(x)`;;

let REAL_EXP_LE_X = `!x. &1 + x <= exp(x)`;;

let REAL_EXP_LT_1 = `!x. &0 < x ==> &1 < exp(x)`;;

let REAL_EXP_MONO_IMP = `!x y. x < y ==> exp(x) < exp(y)`;;

let REAL_EXP_MONO_LT = `!x y. exp(x) < exp(y) <=> x < y`;;

let REAL_EXP_MONO_LE = `!x y. exp(x) <= exp(y) <=> x <= y`;;

let REAL_EXP_INJ = `!x y. (exp(x) = exp(y)) <=> (x = y)`;;

let REAL_EXP_EQ_1 = `!x. exp(x) = &1 <=> x = &0`;;

let REAL_ABS_EXP = `!x. abs(exp x) = exp x`;;

let REAL_EXP_SUM = `!f s. FINITE s ==> exp(sum s f) = product s (\x. exp(f x))`;;

let REAL_EXP_BOUND_LEMMA = `!x. &0 <= x /\ x <= inv(&2) ==> exp(x) <= &1 + &2 * x`;;

(* ------------------------------------------------------------------------- *)
(* Real trig functions, their reality,  derivatives of complex versions.     *)
(* ------------------------------------------------------------------------- *)

let sin = new_definition `sin(x) = Re(csin(Cx x))`;;

let cos = new_definition `cos(x) = Re(ccos(Cx x))`;;

let CNJ_CSIN = `!z. cnj(csin z) = csin(cnj z)`;;

let CNJ_CCOS = `!z. cnj(ccos z) = ccos(cnj z)`;;

let REAL_SIN = `!z. real z ==> real(csin z)`;;

let REAL_COS = `!z. real z ==> real(ccos z)`;;

let CX_SIN = `!x. Cx(sin x) = csin(Cx x)`;;

let CX_COS = `!x. Cx(cos x) = ccos(Cx x)`;;

let HAS_COMPLEX_DERIVATIVE_CSIN = `!z. (csin has_complex_derivative ccos z) (at z)`;;

let COMPLEX_DIFFERENTIABLE_AT_CSIN = `!z. csin complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_CSIN = `!s z. csin complex_differentiable (at z within s)`;;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
             HAS_COMPLEX_DERIVATIVE_CSIN)));;

let HAS_COMPLEX_DERIVATIVE_CCOS = `!z. (ccos has_complex_derivative --csin z) (at z)`;;

let COMPLEX_DIFFERENTIABLE_AT_CCOS = `!z. ccos complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_CCOS = `!s z. ccos complex_differentiable (at z within s)`;;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
             HAS_COMPLEX_DERIVATIVE_CCOS)));;

let CONTINUOUS_AT_CSIN = `!z. csin continuous at z`;;

let CONTINUOUS_WITHIN_CSIN = `!s z. csin continuous (at z within s)`;;

let CONTINUOUS_ON_CSIN = `!s. csin continuous_on s`;;

let HOLOMORPHIC_ON_CSIN = `!s. csin holomorphic_on s`;;

let CONTINUOUS_AT_CCOS = `!z. ccos continuous at z`;;

let CONTINUOUS_WITHIN_CCOS = `!s z. ccos continuous (at z within s)`;;

let CONTINUOUS_ON_CCOS = `!s. ccos continuous_on s`;;

let HOLOMORPHIC_ON_CCOS = `!s. ccos holomorphic_on s`;;

(* ------------------------------------------------------------------------- *)
(* Slew of theorems for compatibility with old transc.ml file.               *)
(* ------------------------------------------------------------------------- *)

let SIN_0 = `sin(&0) = &0`;;

let COS_0 = `cos(&0) = &1`;;

let SIN_CIRCLE = `!x. (sin(x) pow 2) + (cos(x) pow 2) = &1`;;

let SIN_ADD = `!x y. sin(x + y) = sin(x) * cos(y) + cos(x) * sin(y)`;;

let COS_ADD = `!x y. cos(x + y) = cos(x) * cos(y) - sin(x) * sin(y)`;;

let SIN_NEG = `!x. sin(--x) = --(sin(x))`;;

let COS_NEG = `!x. cos(--x) = cos(x)`;;

let SIN_DOUBLE = `!x. sin(&2 * x) = &2 * sin(x) * cos(x)`;;

let COS_DOUBLE = `!x. cos(&2 * x) = (cos(x) pow 2) - (sin(x) pow 2)`;;

let COS_DOUBLE_COS = `!x. cos(&2 * x) = &2 * cos(x) pow 2 - &1`;;

let (SIN_BOUND,COS_BOUND) = (CONJ_PAIR o prove)
 (`(!x. abs(sin x) <= &1) /\ (!x. abs(cos x) <= &1)`,
  CONJ_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN
  MAP_EVERY (MP_TAC o C SPEC REAL_LE_SQUARE) [`sin x`; `cos x`] THEN
  REAL_ARITH_TAC);;

let SIN_BOUNDS = `!x. --(&1) <= sin(x) /\ sin(x) <= &1`;;

let COS_BOUNDS = `!x. --(&1) <= cos(x) /\ cos(x) <= &1`;;

let COS_ABS = `!x. cos(abs x) = cos(x)`;;

let SIN_SUB = `!w z. sin(w - z) = sin(w) * cos(z) - cos(w) * sin(z)`;;

let COS_SUB = `!w z. cos(w - z) = cos(w) * cos(z) + sin(w) * sin(z)`;;

let REAL_MUL_SIN_SIN = `!x y. sin(x) * sin(y) = (cos(x - y) - cos(x + y)) / &2`;;

let REAL_MUL_SIN_COS = `!x y. sin(x) * cos(y) = (sin(x + y) + sin(x - y)) / &2`;;

let REAL_MUL_COS_SIN = `!x y. cos(x) * sin(y) = (sin(x + y) - sin(x - y)) / &2`;;

let REAL_MUL_COS_COS = `!x y. cos(x) * cos(y) = (cos(x - y) + cos(x + y)) / &2`;;

let REAL_ADD_SIN = `!x y. sin(x) + sin(y) = &2 * sin((x + y) / &2) * cos((x - y) / &2)`;;

let REAL_SUB_SIN = `!x y. sin(x) - sin(y) = &2 * sin((x - y) / &2) * cos((x + y) / &2)`;;

let REAL_ADD_COS = `!x y. cos(x) + cos(y) = &2 * cos((x + y) / &2) * cos((x - y) / &2)`;;

let REAL_SUB_COS = `!x y. cos(x) - cos(y) = &2 * sin((x + y) / &2) * sin((y - x) / &2)`;;

let COS_DOUBLE_SIN = `!x. cos(&2 * x) = &1 - &2 * sin x pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Get a nice real/imaginary separation in Euler's formula.                  *)
(* ------------------------------------------------------------------------- *)

let EULER = `!z. cexp(z) = Cx(exp(Re z)) * (Cx(cos(Im z)) + ii * Cx(sin(Im z)))`;;

let RE_CEXP = `!z. Re(cexp z) = exp(Re z) * cos(Im z)`;;

let IM_CEXP = `!z. Im(cexp z) = exp(Re z) * sin(Im z)`;;

let RE_CSIN = `!z. Re(csin z) = (exp(Im z) + exp(--(Im z))) / &2 * sin(Re z)`;;

let IM_CSIN = `!z. Im(csin z) = (exp(Im z) - exp(--(Im z))) / &2 * cos(Re z)`;;

let RE_CCOS = `!z. Re(ccos z) = (exp(Im z) + exp(--(Im z))) / &2 * cos(Re z)`;;

let IM_CCOS = `!z. Im(ccos z) = (exp(--(Im z)) - exp(Im z)) / &2 * sin(Re z)`;;

(* ------------------------------------------------------------------------- *)
(* Some special intermediate value theorems over the reals.                  *)
(* ------------------------------------------------------------------------- *)

let IVT_INCREASING_RE = `!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Re(f(Cx a)) <= y /\ y <= Re(f(Cx b))
        ==> ?x. a <= x /\ x <= b /\ Re(f(Cx x)) = y`;;

let IVT_DECREASING_RE = `!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Re(f(Cx b)) <= y /\ y <= Re(f(Cx a))
        ==> ?x. a <= x /\ x <= b /\ Re(f(Cx x)) = y`;;

let IVT_INCREASING_IM = `!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Im(f(Cx a)) <= y /\ y <= Im(f(Cx b))
        ==> ?x. a <= x /\ x <= b /\ Im(f(Cx x)) = y`;;

let IVT_DECREASING_IM = `!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Im(f(Cx b)) <= y /\ y <= Im(f(Cx a))
        ==> ?x. a <= x /\ x <= b /\ Im(f(Cx x)) = y`;;

(* ------------------------------------------------------------------------- *)
(* Some minimal properties of real logs help to define complex logs.         *)
(* ------------------------------------------------------------------------- *)

let log_def = new_definition
 `log y = @x. exp(x) = y`;;

let EXP_LOG = `!x. &0 < x ==> exp(log x) = x`;;

let LOG_EXP = `!x. log(exp x) = x`;;

let REAL_EXP_LOG = `!x. (exp(log x) = x) <=> &0 < x`;;

let LOG_MUL = `!x y. &0 < x /\ &0 < y ==> (log(x * y) = log(x) + log(y))`;;

let LOG_INJ = `!x y. &0 < x /\ &0 < y ==> (log(x) = log(y) <=> x = y)`;;

let LOG_1 = `log(&1) = &0`;;

let LOG_INV = `!x. &0 < x ==> (log(inv x) = --(log x))`;;

let LOG_DIV = `!x y. &0 < x /\ &0 < y ==> log(x / y) = log(x) - log(y)`;;

let LOG_MONO_LT = `!x y. &0 < x /\ &0 < y ==> (log(x) < log(y) <=> x < y)`;;

let LOG_MONO_LT_IMP = `!x y. &0 < x /\ x < y ==> log(x) < log(y)`;;

let LOG_MONO_LT_REV = `!x y. &0 < x /\ &0 < y /\ log x < log y ==> x < y`;;

let LOG_MONO_LE = `!x y. &0 < x /\ &0 < y ==> (log(x) <= log(y) <=> x <= y)`;;

let LOG_MONO_LE_IMP = `!x y. &0 < x /\ x <= y ==> log(x) <= log(y)`;;

let LOG_MONO_LE_REV = `!x y. &0 < x /\ &0 < y /\ log x <= log y ==> x <= y`;;

let LOG_POW = `!n x. &0 < x ==> (log(x pow n) = &n * log(x))`;;

let LOG_LE_STRONG = `!x. &0 < &1 + x ==> log(&1 + x) <= x`;;

let LOG_LE = `!x. &0 <= x ==> log(&1 + x) <= x`;;

let LOG_LT_X = `!x. &0 < x ==> log(x) < x`;;

let LOG_POS = `!x. &1 <= x ==> &0 <= log(x)`;;

let LOG_POS_LT = `!x. &1 < x ==> &0 < log(x)`;;

let LOG_PRODUCT = `!f:A->real s.
        FINITE s /\ (!x. x IN s ==> &0 < f x)
        ==> log(product s f) = sum s (\x. log(f x))`;;

(* ------------------------------------------------------------------------- *)
(* Deduce periodicity just from derivative and zero values.                  *)
(* ------------------------------------------------------------------------- *)

let SIN_NEARZERO = `?x. &0 < x /\ !y. &0 < y /\ y <= x ==> &0 < sin(y)`;;

let SIN_NONTRIVIAL = `?x. &0 < x /\ ~(sin x = &0)`;;

let COS_NONTRIVIAL = `?x. &0 < x /\ ~(cos x = &1)`;;

let COS_DOUBLE_BOUND = `!x. &0 <= cos x ==> &2 * (&1 - cos x) <= &1 - cos(&2 * x)`;;

let COS_GOESNEGATIVE_LEMMA = `!x. cos(x) < &1 ==> ?n. cos(&2 pow n * x) < &0`;;

let COS_GOESNEGATIVE = `?x. &0 < x /\ cos(x) < &0`;;

let COS_HASZERO = `?x. &0 < x /\ cos(x) = &0`;;

let SIN_HASZERO = `?x. &0 < x /\ sin(x) = &0`;;

let SIN_HASZERO_MINIMAL = `?p. &0 < p /\ sin p = &0 /\ !x. &0 < x /\ x < p ==> ~(sin x = &0)`;;

let pi = new_definition
 `pi = @p. &0 < p /\ sin(p) = &0 /\ !x. &0 < x /\ x < p ==> ~(sin(x) = &0)`;;

let PI_WORKS = `&0 < pi /\ sin(pi) = &0 /\ !x. &0 < x /\ x < pi ==> ~(sin x = &0)`;;

(* ------------------------------------------------------------------------- *)
(* Now more relatively easy consequences.                                    *)
(* ------------------------------------------------------------------------- *)

let PI_POS = `&0 < pi`;;

let PI_POS_LE = `&0 <= pi`;;

let PI_NZ = `~(pi = &0)`;;

let REAL_ABS_PI = `abs pi = pi`;;

let SIN_PI = `sin(pi) = &0`;;

let SIN_POS_PI = `!x. &0 < x /\ x < pi ==> &0 < sin(x)`;;

let COS_PI2 = `cos(pi / &2) = &0`;;

let COS_PI = `cos(pi) = -- &1`;;

let SIN_PI2 = `sin(pi / &2) = &1`;;

let SIN_COS = `!x. sin(x) = cos(pi / &2 - x)`;;

let COS_SIN = `!x. cos(x) = sin(pi / &2 - x)`;;

let SIN_PERIODIC_PI = `!x. sin(x + pi) = --(sin(x))`;;

let COS_PERIODIC_PI = `!x. cos(x + pi) = --(cos(x))`;;

let SIN_PERIODIC = `!x. sin(x + &2 * pi) = sin(x)`;;

let COS_PERIODIC = `!x. cos(x + &2 * pi) = cos(x)`;;

let SIN_NPI = `!n. sin(&n * pi) = &0`;;

let COS_NPI = `!n. cos(&n * pi) = --(&1) pow n`;;

let COS_POS_PI2 = `!x. &0 < x /\ x < pi / &2 ==> &0 < cos(x)`;;

let SIN_POS_PI2 = `!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)`;;

let COS_POS_PI = `!x. --(pi / &2) < x /\ x < pi / &2 ==> &0 < cos(x)`;;

let COS_POS_PI_LE = `!x. --(pi / &2) <= x /\ x <= pi / &2 ==> &0 <= cos(x)`;;

let SIN_POS_PI_LE = `!x. &0 <= x /\ x <= pi ==> &0 <= sin(x)`;;

let SIN_PIMUL_EQ_0 = `!n. sin(n * pi) = &0 <=> integer(n)`;;

let SIN_EQ_0 = `!x. sin(x) = &0 <=> ?n. integer n /\ x = n * pi`;;

let COS_EQ_0 = `!x. cos(x) = &0 <=> ?n. integer n /\ x = (n + &1 / &2) * pi`;;

let SIN_ZERO_PI = `!x. sin(x) = &0 <=> (?n. x = &n * pi) \/ (?n. x = --(&n * pi))`;;

let COS_ZERO_PI = `!x. cos(x) = &0 <=>
       (?n. x = (&n + &1 / &2) * pi) \/ (?n. x = --((&n + &1 / &2) * pi))`;;

let SIN_ZERO = `!x. (sin(x) = &0) <=> (?n. EVEN n /\ x = &n * (pi / &2)) \/
                         (?n. EVEN n /\ x = --(&n * (pi / &2)))`;;

let COS_ZERO = `!x. cos(x) = &0 <=> (?n. ~EVEN n /\ (x = &n * (pi / &2))) \/
                       (?n. ~EVEN n /\ (x = --(&n * (pi / &2))))`;;

let COS_ONE_2PI = `!x. (cos(x) = &1) <=> (?n. x = &n * &2 * pi) \/ (?n. x = --(&n * &2 * pi))`;;

let SIN_COS_SQRT = `!x. &0 <= sin(x) ==> (sin(x) = sqrt(&1 - (cos(x) pow 2)))`;;

let SIN_EQ_0_PI = `!x. --pi < x /\ x < pi /\ sin(x) = &0 ==> x = &0`;;

let COS_TREBLE_COS = `!x. cos(&3 * x) = &4 * cos(x) pow 3 - &3 * cos x`;;

let COS_PI6 = `cos(pi / &6) = sqrt(&3) / &2`;;

let SIN_PI6 = `sin(pi / &6) = &1 / &2`;;

let SIN_POS_PI_REV = `!x. &0 <= x /\ x <= &2 * pi /\ &0 < sin x ==> &0 < x /\ x < pi`;;

let SIN_PI3 = `sin(pi / &3) = sqrt(&3) / &2`;;

let COS_PI3 = `cos(pi / &3) = &1 / &2`;;

let CEXP_II_PI = `cexp(ii * Cx pi) = --Cx(&1)`;;

(* ------------------------------------------------------------------------- *)
(* Prove totality of trigs.                                                  *)
(* ------------------------------------------------------------------------- *)

let SIN_TOTAL_POS = `!y. &0 <= y /\ y <= &1
       ==> ?x. &0 <= x /\ x <= pi / &2 /\ sin(x) = y`;;

let SINCOS_TOTAL_PI2 = `!x y. &0 <= x /\ &0 <= y /\ x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t <= pi / &2 /\ x = cos t /\ y = sin t`;;

let SINCOS_TOTAL_PI = `!x y. &0 <= y /\ x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t <= pi /\ x = cos t /\ y = sin t`;;

let SINCOS_TOTAL_2PI = `!x y. x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t < &2 * pi /\ x = cos t /\ y = sin t`;;

let CIRCLE_SINCOS = `!x y. x pow 2 + y pow 2 = &1 ==> ?t. x = cos(t) /\ y = sin(t)`;;

(* ------------------------------------------------------------------------- *)
(* Polar representation.                                                     *)
(* ------------------------------------------------------------------------- *)

let CX_PI_NZ = `~(Cx pi = Cx(&0))`;;

let COMPLEX_UNIMODULAR_POLAR = `!z. (norm z = &1) ==> ?x. z = complex(cos(x),sin(x))`;;

let SIN_INTEGER_2PI = `!n. integer n ==> sin((&2 * pi) * n) = &0`;;

let SIN_INTEGER_PI = `!n. integer n ==> sin (n * pi) = &0`;;

let COS_INTEGER_2PI = `!n. integer n ==> cos((&2 * pi) * n) = &1`;;

let SINCOS_PRINCIPAL_VALUE = `!x. ?y. (--pi < y /\ y <= pi) /\ (sin(y) = sin(x) /\ cos(y) = cos(x))`;;

let CEXP_COMPLEX = `!r t. cexp(complex(r,t)) = Cx(exp r) * complex(cos t,sin t)`;;

let NORM_COSSIN = `!t. norm(complex(cos t,sin t)) = &1`;;

let NORM_CEXP = `!z. norm(cexp z) = exp(Re z)`;;

let NORM_CEXP_II = `!t. norm (cexp (ii * Cx t)) = &1`;;

let NORM_CEXP_IMAGINARY = `!z. norm(cexp z) = &1 ==> Re(z) = &0`;;

let CEXP_EQ_1 = `!z. cexp z = Cx(&1) <=> Re(z) = &0 /\ ?n. integer n /\ Im(z) = &2 * n * pi`;;

let CEXP_EQ = `!w z. cexp w = cexp z <=> ?n. integer n /\ w = z + Cx(&2 * n * pi) * ii`;;

let COMPLEX_EQ_CEXP = `!w z. abs(Im w - Im z) < &2 * pi /\ cexp w = cexp z ==> w = z`;;

let CEXP_INTEGER_2PI = `!n. integer n ==> cexp(Cx(&2 * n * pi) * ii) = Cx(&1)`;;

let CEXP_LIPSCHITZ_BOUNDED = `!M a b. norm(a) <= M /\ norm(b) <= M
           ==> norm(cexp a - cexp b) <= exp(M) * norm(a - b)`;;

let SIN_COS_EQ = `!x y. sin y = sin x /\ cos y = cos x <=>
         ?n. integer n /\ y = x + &2 * n * pi`;;

let SIN_COS_INJ = `!x y. sin x = sin y /\ cos x = cos y /\ abs(x - y) < &2 * pi ==> x = y`;;

let CEXP_II_NE_1 = `!x. &0 < x /\ x < &2 * pi ==> ~(cexp(ii * Cx x) = Cx(&1))`;;

let CSIN_EQ_0 = `!z. csin z = Cx(&0) <=> ?n. integer n /\ z = Cx(n * pi)`;;

let CCOS_EQ_0 = `!z. ccos z = Cx(&0) <=> ?n. integer n /\ z = Cx((n + &1 / &2) * pi)`;;

let CCOS_EQ_1 = `!z. ccos z = Cx(&1) <=> ?n. integer n /\ z = Cx(&2 * n * pi)`;;

let CSIN_EQ_1 = `!z. csin z = Cx(&1) <=> ?n. integer n /\ z = Cx((&2 * n + &1 / &2) * pi)`;;

let CSIN_EQ_MINUS1 = `!z. csin z = --Cx(&1) <=>
       ?n. integer n /\ z = Cx((&2 * n + &3 / &2) * pi)`;;

let CCOS_EQ_MINUS1 = `!z. ccos z = --Cx(&1) <=>
       ?n. integer n /\ z = Cx((&2 * n + &1) * pi)`;;

let COS_EQ_1 = `!x. cos x = &1 <=> ?n. integer n /\ x = &2 * n * pi`;;

let SIN_EQ_1 = `!x. sin x = &1 <=> ?n. integer n /\ x = (&2 * n + &1 / &2) * pi`;;

let SIN_EQ_MINUS1 = `!x. sin x = --(&1) <=> ?n. integer n /\ x = (&2 * n + &3 / &2) * pi`;;

let COS_EQ_MINUS1 = `!x. cos x = --(&1) <=>
       ?n. integer n /\ x = (&2 * n + &1) * pi`;;

let DIST_CEXP_II_1 = `!t. norm(cexp(ii * Cx t) - Cx(&1)) = &2 * abs(sin(t / &2))`;;

let CX_SINH = `Cx((exp x - inv(exp x)) / &2) = --ii * csin(ii * Cx x)`;;

let CX_COSH = `Cx((exp x + inv(exp x)) / &2) = ccos(ii * Cx x)`;;

let NORM_CCOS_POW_2 = `!z. norm(ccos z) pow 2 =
       cos(Re z) pow 2 + (exp(Im z) - inv(exp(Im z))) pow 2 / &4`;;

let NORM_CSIN_POW_2 = `!z. norm(csin z) pow 2 =
       (exp(&2 * Im z) + inv(exp(&2 * Im z)) - &2 * cos(&2 * Re z)) / &4`;;

let CSIN_EQ = `!w z. csin w = csin z <=>
         ?n. integer n /\
             (w = z + Cx(&2 * n * pi) \/ w = --z + Cx((&2 * n + &1) * pi))`;;

let CCOS_EQ = `!w z. ccos(w) = ccos(z) <=>
         ?n. integer n /\
             (w = z + Cx(&2 * n * pi) \/ w = --z + Cx(&2 * n * pi))`;;

let SIN_EQ = `!x y. sin x = sin y <=>
         ?n. integer n /\
             (x = y + &2 * n * pi \/ x = --y + (&2 * n + &1) * pi)`;;

let COS_EQ = `!x y. cos x = cos y <=>
         ?n. integer n /\
             (x = y + &2 * n * pi \/ x = --y + &2 * n * pi)`;;

let NORM_CCOS_LE = `!z. norm(ccos z) <= exp(norm z)`;;

let NORM_CCOS_PLUS1_LE = `!z. norm(Cx(&1) + ccos z) <= &2 * exp(norm z)`;;

(* ------------------------------------------------------------------------- *)
(* Taylor series for complex exponential.                                    *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_CEXP = `!n z. norm(cexp z - vsum(0..n) (\k. z pow k / Cx(&(FACT k))))
         <= exp(abs(Re z)) * (norm z) pow (n + 1) / &(FACT n)`;;

(* ------------------------------------------------------------------------- *)
(* Approximation to e.                                                       *)
(* ------------------------------------------------------------------------- *)

let E_APPROX_32 = `abs(exp(&1) - &5837465777 / &2147483648) <= inv(&2 pow 32)`;;

(* ------------------------------------------------------------------------- *)
(* Taylor series for complex sine and cosine.                                *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_CSIN_RAW = `!n z. norm(csin z -
              vsum(0..n) (\k. if ODD k
                              then --ii * (ii * z) pow k / Cx(&(FACT k))
                              else Cx(&0)))
         <= exp(abs(Im z)) * (norm z) pow (n + 1) / &(FACT n)`;;

let TAYLOR_CSIN = `!n z. norm(csin z -
              vsum(0..n) (\k. --Cx(&1) pow k *
                              z pow (2 * k + 1) / Cx(&(FACT(2 * k + 1)))))
         <= exp(abs(Im z)) * norm(z) pow (2 * n + 3) / &(FACT(2 * n + 2))`;;

let CSIN_CONVERGES = `!z. ((\n. --Cx(&1) pow n * z pow (2 * n + 1) / Cx(&(FACT(2 * n + 1))))
        sums csin(z)) (from 0)`;;

let TAYLOR_CCOS_RAW = `!n z. norm(ccos z -
              vsum(0..n) (\k. if EVEN k
                              then (ii * z) pow k / Cx(&(FACT k))
                              else Cx(&0)))
         <= exp(abs(Im z)) * (norm z) pow (n + 1) / &(FACT n)`;;

let TAYLOR_CCOS = `!n z. norm(ccos z -
              vsum(0..n) (\k. --Cx(&1) pow k *
                              z pow (2 * k) / Cx(&(FACT(2 * k)))))
         <= exp(abs(Im z)) * norm(z) pow (2 * n + 2) / &(FACT(2 * n + 1))`;;

let CCOS_CONVERGES = `!z. ((\n. --Cx(&1) pow n * z pow (2 * n) / Cx(&(FACT(2 * n))))
        sums ccos(z)) (from 0)`;;

(* ------------------------------------------------------------------------- *)
(* The argument of a complex number, where 0 <= arg(z) < 2 pi                *)
(* ------------------------------------------------------------------------- *)

let Arg_DEF = new_definition
 `Arg z = if z = Cx(&0) then &0
          else @t. &0 <= t /\ t < &2 * pi /\
                   z = Cx(norm(z)) * cexp(ii * Cx t)`;;

let ARG_0 = `Arg(Cx(&0)) = &0`;;

let ARG = `!z. &0 <= Arg(z) /\ Arg(z) < &2 * pi /\
       z = Cx(norm z) * cexp(ii * Cx(Arg z))`;;

let COMPLEX_NORM_EQ_1_CEXP = `!z. norm z = &1 <=> (?t. z = cexp(ii * Cx t))`;;

let ARG_UNIQUE = `!a r z. &0 < r /\ Cx r * cexp(ii * Cx a) = z /\ &0 <= a /\ a < &2 * pi
           ==> Arg z = a`;;

let ARG_MUL_CX = `!r z. &0 < r ==> Arg(Cx r * z) = Arg(z)`;;

let ARG_DIV_CX = `!r z. &0 < r ==> Arg(z / Cx r) = Arg(z)`;;

let ARG_LT_NZ = `!z. &0 < Arg z <=> ~(Arg z = &0)`;;

let ARG_LE_PI = `!z. Arg z <= pi <=> &0 <= Im z`;;

let ARG_LT_PI = `!z. &0 < Arg z /\ Arg z < pi <=> &0 < Im z`;;

let ARG_EQ_0 = `!z. Arg z = &0 <=> real z /\ &0 <= Re z`;;

let ARG_NUM = `!n. Arg(Cx(&n)) = &0`;;

let ARG_EQ_PI = `!z. Arg z = pi <=> real z /\ Re z < &0`;;

let ARG_EQ_0_PI = `!z. Arg z = &0 \/ Arg z = pi <=> real z`;;

let ARG_INV = `!z. ~(real z /\ &0 <= Re z) ==> Arg(inv z) = &2 * pi - Arg z`;;

let ARG_EQ = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> (Arg w = Arg z <=> ?x. &0 < x /\ w = Cx(x) * z)`;;

let ARG_INV_EQ_0 = `!z. Arg(inv z) = &0 <=> Arg z = &0`;;

let ARG_LE_DIV_SUM = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) /\ Arg(w) <= Arg(z)
         ==> Arg(z) = Arg(w) + Arg(z / w)`;;

let ARG_LE_DIV_SUM_EQ = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> (Arg(w) <= Arg(z) <=> Arg(z) = Arg(w) + Arg(z / w))`;;

let REAL_SUB_ARG = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg w - Arg z = if Arg(z) <= Arg(w) then Arg(w / z)
                             else Arg(w / z) - &2 * pi`;;

let REAL_ADD_ARG = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg(w) + Arg(z) =
             if Arg w + Arg z < &2 * pi
             then Arg(w * z)
             else Arg(w * z) + &2 * pi`;;

let ARG_MUL = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg(w * z) = if Arg w + Arg z < &2 * pi
                          then Arg w + Arg z
                          else (Arg w + Arg z) - &2 * pi`;;

let ARG_CNJ = `!z. Arg(cnj z) = if real z /\ &0 <= Re z then Arg z else &2 * pi - Arg z`;;

let ARG_REAL = `!z. real z ==> Arg z = if &0 <= Re z then &0 else pi`;;

let ARG_CEXP = `!z. &0 <= Im z /\ Im z < &2 * pi ==> Arg(cexp(z)) = Im z`;;

(* ------------------------------------------------------------------------- *)
(* Properties of 2-D rotations, and their interpretation using cexp.         *)
(* ------------------------------------------------------------------------- *)

let rotate2d = new_definition
 `(rotate2d:real->real^2->real^2) t x =
        vector[x$1 * cos(t) - x$2 * sin(t);
               x$1 * sin(t) + x$2 * cos(t)]`;;

let LINEAR_ROTATE2D = `!t. linear(rotate2d t)`;;

let ROTATE2D_ADD_VECTORS = `!t w z. rotate2d t (w + z) = rotate2d t w + rotate2d t z`;;

let ROTATE2D_SUB = `!t w z. rotate2d t (w - z) = rotate2d t w - rotate2d t z`;;

let NORM_ROTATE2D = `!t z. norm(rotate2d t z) = norm z`;;

let ROTATE2D_0 = `!t. rotate2d t (Cx(&0)) = Cx(&0)`;;

let ROTATE2D_EQ_0 = `!t z. rotate2d t z = Cx(&0) <=> z = Cx(&0)`;;

let ROTATE2D_ZERO = `!z. rotate2d (&0) z = z`;;

let ORTHOGONAL_TRANSFORMATION_ROTATE2D = `!t. orthogonal_transformation(rotate2d t)`;;

let ROTATE2D_POLAR = `!r t s. rotate2d t (vector[r * cos(s); r * sin(s)]) =
                        vector[r * cos(t + s); r * sin(t + s)]`;;

let MATRIX_ROTATE2D = `!t. matrix(rotate2d t) = vector[vector[cos t;--(sin t)];
                                   vector[sin t; cos t]]`;;

let DET_MATRIX_ROTATE2D = `!t. det(matrix(rotate2d t)) = &1`;;

let ROTATION_ROTATE2D = `!f. orthogonal_transformation f /\ det(matrix f) = &1
       ==> ?t. &0 <= t /\ t < &2 * pi /\ f = rotate2d t`;;

let ROTATE2D_ADD = `!s t x. rotate2d (s + t) x = rotate2d s (rotate2d t x)`;;

let ROTATE2D_COMPLEX = `!t z. rotate2d t z = cexp(ii * Cx t) * z`;;

let ROTATE2D_PI2 = `!z. rotate2d (pi / &2) z = ii * z`;;

let ROTATE2D_PI = `!z. rotate2d pi z = --z`;;

let ROTATE2D_NPI = `!n z. rotate2d (&n * pi) z = --Cx(&1) pow n * z`;;

let ROTATE2D_2PI = `!z. rotate2d (&2 * pi) z = z`;;

let ARG_ROTATE2D = `!t z. ~(z = Cx(&0)) /\ &0 <= t + Arg z /\ t + Arg z < &2 * pi
         ==> Arg(rotate2d t z) = t + Arg z`;;

let ARG_ROTATE2D_UNIQUE = `!t a z. ~(z = Cx(&0)) /\ Arg(rotate2d t z) = a
           ==> ?n. integer n /\ t = &2 * n * pi + (a - Arg z)`;;

let ARG_ROTATE2D_UNIQUE_2PI = `!s t z. ~(z = Cx(&0)) /\
           &0 <= s /\ s < &2 * pi /\ &0 <= t /\ t < &2 * pi /\
           Arg(rotate2d s z) = Arg(rotate2d t z)
           ==> s = t`;;

let COMPLEX_DIV_ROTATION = `!f w z. orthogonal_transformation f /\ det(matrix f) = &1
           ==> f w / f z = w / z`;;

let th = `!f w z. linear f /\ (!x. norm(f x) = norm x) /\
           (2 <= dimindex(:2) ==> det(matrix f) = &1)
           ==> f w / f z = w / z`;;

let ROTATION_ROTATE2D_EXISTS = `!x y. norm x = norm y ==> ?t. &0 <= t /\ t < &2 * pi /\ rotate2d t x = y`;;

let ROTATION_ROTATE2D_EXISTS_ORTHOGONAL = `!e1 e2. norm(e1) = &1 /\ norm(e2) = &1 /\ orthogonal e1 e2
           ==> e1 = rotate2d (pi / &2) e2 \/ e2 = rotate2d (pi / &2) e1`;;

let ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED = `!e1 e2. norm(e1) = &1 /\ norm(e2) = &1 /\ orthogonal e1 e2 /\
           &0 < e1$1 * e2$2 - e1$2 * e2$1
           ==> e2 = rotate2d (pi / &2) e1`;;

let ROTATE2D_EQ = `!t x y. rotate2d t x = rotate2d t y <=> x = y`;;

let ROTATE2D_SUB_ARG = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> rotate2d(Arg w - Arg z) = rotate2d(Arg(w / z))`;;

let ROTATION_MATRIX_ROTATE2D = `!t. rotation_matrix(matrix(rotate2d t))`;;

let ROTATION_MATRIX_ROTATE2D_EQ = `!A:real^2^2. rotation_matrix A <=> ?t. A = matrix(rotate2d t)`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy of linear maps of various kinds where the homotopy stays inside  *)
(* that class of linear maps.                                                *)
(* ------------------------------------------------------------------------- *)

let NULLHOMOTOPIC_ORTHOGONAL_TRANSFORMATION = `!f:real^N->real^N.
       orthogonal_transformation f /\ det(matrix f) = &1
       ==> homotopic_with orthogonal_transformation
            (subtopology euclidean (:real^N),subtopology euclidean (:real^N))
            f I`;;

let HOMOTOPIC_SPECIAL_ORTHOGONAL_TRANSFORMATIONS,
    HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV = (CONJ_PAIR o prove)
 (`(!f g. homotopic_with
            (\h. orthogonal_transformation h /\ det(matrix h) = det(matrix f))
            (subtopology euclidean (:real^N),subtopology euclidean (:real^N))
            f g <=>
          homotopic_with
            orthogonal_transformation
             (subtopology euclidean (:real^N),
              subtopology euclidean (:real^N)) f g) /\
   !f g. homotopic_with orthogonal_transformation
          (subtopology euclidean (:real^N),
           subtopology euclidean (:real^N)) f g <=>
         orthogonal_transformation f /\ orthogonal_transformation g /\
         det(matrix f) = det(matrix g)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(u ==> s) /\ (s ==> t) /\ (t ==> u)
    ==> (u <=> t) /\ (t <=> s)`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN MESON_TAC[];
    STRIP_TAC THEN
    MP_TAC(ISPEC `g:real^N->real^N` ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(f:real^N->real^N) = g o (h:real^N->real^N) o f /\ g = g o I`
     (fun th -> ONCE_REWRITE_TAC[th])
    THENL [ASM_REWRITE_TAC[o_ASSOC; I_O_ID]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; LINEAR_CONTINUOUS_ON] THEN
    SUBGOAL_THEN
      `!k:real^N->real^N.
          orthogonal_transformation (g o k) <=> orthogonal_transformation k`
      (fun th -> REWRITE_TAC[th; ETA_AX])
    THENL
     [GEN_TAC THEN EQ_TAC THEN
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE] THEN DISCH_THEN
       (MP_TAC o SPEC `h:real^N->real^N` o MATCH_MP (ONCE_REWRITE_RULE
         [IMP_CONJ_ALT] ORTHOGONAL_TRANSFORMATION_COMPOSE)) THEN
      ASM_SIMP_TAC[o_ASSOC; I_O_ID];
      MATCH_MP_TAC NULLHOMOTOPIC_ORTHOGONAL_TRANSFORMATION THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM
       `\f:real^N->real^N. det(matrix f)`)) THEN
      ASM_SIMP_TAC[MATRIX_COMPOSE; ORTHOGONAL_TRANSFORMATION_LINEAR;
                   ORTHOGONAL_TRANSFORMATION_COMPOSE; DET_MUL;
                   MATRIX_I; DET_I]];
    REWRITE_TAC[HOMOTOPIC_WITH_EUCLIDEAN] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:real^(1,N)finite_sum->real^N` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN MP_TAC(ISPECL
     [`\t. lift(
       det(matrix((k:real^(1,N)finite_sum->real^N) o pastecart t)))`;
      `interval[vec 0:real^1,vec 1]`]
     CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
    REWRITE_TAC[CONNECTED_INTERVAL] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
        SIMP_TAC[matrix; LAMBDA_BETA; o_DEF] THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
        ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
                 CONTINUOUS_ON_ID] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_UNIV];
        X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `u:real^1` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; LIFT_EQ] THEN
        SUBGOAL_THEN
         `orthogonal_transformation
           ((k:real^(1,N)finite_sum->real^N) o pastecart t) /\
          orthogonal_transformation (k o pastecart u)`
        MP_TAC THENL [ASM_SIMP_TAC[o_DEF]; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN
          (STRIP_ASSUME_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX o
                    MATCH_MP ORTHOGONAL_MATRIX_MATRIX)) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      REWRITE_TAC[o_DEF; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `a:real^1` THEN DISCH_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM])) THEN
      REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
      ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL; GSYM LIFT_EQ]]]);;

let HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_SPHERE = `!f g r.
        &0 < r
        ==> (homotopic_with orthogonal_transformation
              (subtopology euclidean (sphere(vec 0,r)),
               subtopology euclidean (sphere(vec 0,r))) f g <=>
             homotopic_with orthogonal_transformation
              (subtopology euclidean (:real^N),
               subtopology euclidean (:real^N)) f g)`;;

let HOMOTOPIC_LINEAR_MAPS = `!f g. homotopic_with linear
          (subtopology euclidean (:real^M),subtopology euclidean (:real^N))
          f g <=>
         linear f /\ linear g`;;

let HOMOTOPIC_LINEAR_POSITIVE_SEMIDEFINITE_MAPS = `!f g. homotopic_with (\f. linear f /\ positive_semidefinite(matrix f))
          (subtopology euclidean (:real^N),
           subtopology euclidean (:real^N)) f g <=>
           linear f /\ linear g /\
           positive_semidefinite(matrix f) /\
           positive_semidefinite(matrix g)`;;

let HOMOTOPIC_LINEAR_POSITIVE_DEFINITE_MAPS = `!f g. homotopic_with (\f. linear f /\ positive_definite(matrix f))
           (subtopology euclidean (:real^N),
            subtopology euclidean (:real^N)) f g <=>
           linear f /\ linear g /\
           positive_definite(matrix f) /\
           positive_definite(matrix g)`;;

let HOMOTOPIC_RESTRICTED_LINEAR_MAPS = `!f g b. homotopic_with (\f. linear f /\ real_sgn(det(matrix f)) = b)
            (subtopology euclidean (:real^N),
             subtopology euclidean (:real^N)) f g <=>
           linear f /\ linear g /\
           real_sgn(det(matrix f)) = b /\
           real_sgn(det(matrix g)) = b`;;

let HOMOTOPIC_INVERTIBLE_LINEAR_MAPS_ALT = `!f g. homotopic_with (\h. linear h /\ invertible(matrix h))
          (subtopology euclidean (:real^N),
           subtopology euclidean (:real^N)) f g <=>
         linear f /\ linear g /\
         &0 < real_sgn(det(matrix f)) * real_sgn(det(matrix g))`;;

let HOMOTOPIC_INVERTIBLE_LINEAR_MAPS = `!f g. homotopic_with (\h. linear h /\ invertible(matrix h))
          (subtopology euclidean (:real^N),
           subtopology euclidean (:real^N)) f g <=>
         linear f /\ linear g /\ &0 < det(matrix f) * det(matrix g)`;;

(* ------------------------------------------------------------------------- *)
(* "If and only if" variants of unrestricted homotopy characterization       *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_LINEAR_MAPS_EQ = `!f g:real^N->real^N.
        linear f /\ linear g
        ==> (homotopic_with (\x. T)
               (subtopology euclidean ((:real^N) DELETE vec 0),
                subtopology euclidean ((:real^N) DELETE vec 0)) f g <=>
             &0 < det(matrix f) * det(matrix g))`;;

let HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_EQ = `!f g:real^N->real^N.
        orthogonal_transformation f /\ orthogonal_transformation g
        ==> (homotopic_with (\x. T)
              (subtopology euclidean (sphere (vec 0,&1)),
               subtopology euclidean (sphere (vec 0,&1))) f g <=>
             det(matrix f) = det(matrix g))`;;

let HOMOTOPIC_ANTIPODAL_IDENTITY_MAP = `homotopic_with (\x. T)
      (subtopology euclidean (sphere(vec 0,&1)),
       subtopology euclidean (sphere(vec 0,&1)))
                  (\x:real^N. --x) (\x. x) <=>
   EVEN(dimindex(:N))`;;

(* ------------------------------------------------------------------------- *)
(* Complex tangent function.                                                 *)
(* ------------------------------------------------------------------------- *)

let ctan = new_definition
 `ctan z = csin z / ccos z`;;

let CTAN_0 = `ctan(Cx(&0)) = Cx(&0)`;;

let CTAN_NEG = `!z. ctan(--z) = --(ctan z)`;;

let CTAN_ADD = `!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0)) /\
         ~(ccos(w + z) = Cx(&0))
         ==> ctan(w + z) = (ctan w + ctan z) / (Cx(&1) - ctan(w) * ctan(z))`;;

let CTAN_DOUBLE = `!z. ctan(Cx(&2) * z) = (Cx(&2) * ctan z) / (Cx(&1) - ctan z pow 2)`;;

let CCOT_DOUBLE = `!z. inv(ctan(Cx(&2) * z)) = (inv(ctan z) - ctan z) / Cx(&2)`;;

let CTAN_CCOT_DOUBLE = `!z. ctan z = Cx(&1) / ctan z - Cx(&2) / ctan(Cx(&2) * z)`;;

let CTAN_SUB = `!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0)) /\
         ~(ccos(w - z) = Cx(&0))
         ==> ctan(w - z) = (ctan w - ctan z) / (Cx(&1) + ctan(w) * ctan(z))`;;

let COMPLEX_ADD_CTAN = `!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0))
         ==> ctan(w) + ctan(z) = csin(w + z) / (ccos(w) * ccos(z))`;;

let COMPLEX_SUB_CTAN = `!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0))
         ==> ctan(w) - ctan(z) = csin(w - z) / (ccos(w) * ccos(z))`;;

let CTAN_CEXP = `!z. ctan z =
       --ii * (cexp(Cx(&2) * ii * z) - Cx(&1)) /
              (cexp(Cx(&2) * ii * z) + Cx(&1))`;;

(* ------------------------------------------------------------------------- *)
(* Analytic properties of tangent function.                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_CTAN = `!z. ~(ccos z = Cx(&0))
       ==> (ctan has_complex_derivative (inv(ccos(z) pow 2))) (at z)`;;

let COMPLEX_DIFFERENTIABLE_AT_CTAN = `!z. ~(ccos z = Cx(&0)) ==> ctan complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_CTAN = `!s z. ~(ccos z = Cx(&0))
         ==> ctan complex_differentiable (at z within s)`;;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CTAN)));;

let CONTINUOUS_AT_CTAN = `!z. ~(ccos z = Cx(&0)) ==> ctan continuous at z`;;

let CONTINUOUS_WITHIN_CTAN = `!s z. ~(ccos z = Cx(&0)) ==> ctan continuous (at z within s)`;;

let CONTINUOUS_ON_CTAN = `!s. (!z. z IN s ==> ~(ccos z = Cx(&0))) ==> ctan continuous_on s`;;

let HOLOMORPHIC_ON_CTAN = `!s. (!z. z IN s ==> ~(ccos z = Cx(&0))) ==> ctan holomorphic_on s`;;

(* ------------------------------------------------------------------------- *)
(* Real tangent function.                                                    *)
(* ------------------------------------------------------------------------- *)

let tan_def = new_definition
 `tan(x) = Re(ctan(Cx x))`;;

let CNJ_CTAN = `!z. cnj(ctan z) = ctan(cnj z)`;;

let REAL_TAN = `!z. real z ==> real(ctan z)`;;

let CX_TAN = `!x. Cx(tan x) = ctan(Cx x)`;;

let tan = `!x. tan x = sin x / cos x`;;

let TAN_0 = `tan(&0) = &0`;;

let TAN_PI = `tan(pi) = &0`;;

let TAN_NPI = `!n. tan(&n * pi) = &0`;;

let TAN_NEG = `!x. tan(--x) = --(tan x)`;;

let TAN_PERIODIC_PI = `!x. tan(x + pi) = tan(x)`;;

let TAN_PERIODIC_NPI = `!x n. tan(x + &n * pi) = tan(x)`;;

let TAN_ADD = `!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x + y) = &0)
         ==> tan(x + y) = (tan(x) + tan(y)) / (&1 - tan(x) * tan(y))`;;

let TAN_SUB = `!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x - y) = &0)
         ==> tan(x - y) = (tan(x) - tan(y)) / (&1 + tan(x) * tan(y))`;;

let TAN_DOUBLE = `!x. tan(&2 * x) = (&2 * tan x) / (&1 - tan x pow 2)`;;

let COT_DOUBLE = `!z. inv(tan(&2 * z)) = (inv(tan z) - tan z) / &2`;;

let TAN_COT_DOUBLE = `!z. tan z = &1 / tan z - &2 / tan(&2 * z)`;;

let REAL_ADD_TAN = `!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0)
         ==> tan(x) + tan(y) = sin(x + y) / (cos(x) * cos(y))`;;

let REAL_SUB_TAN = `!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0)
         ==> tan(x) - tan(y) = sin(x - y) / (cos(x) * cos(y))`;;

let TAN_PI4 = `tan(pi / &4) = &1`;;

let TAN_POS_PI2 = `!x. &0 < x /\ x < pi / &2 ==> &0 < tan x`;;

let TAN_POS_PI2_LE = `!x. &0 <= x /\ x < pi / &2 ==> &0 <= tan x`;;

let COS_TAN = `!x. abs(x) < pi / &2 ==> cos(x) = &1 / sqrt(&1 + tan(x) pow 2)`;;

let SIN_TAN = `!x. abs(x) < pi / &2 ==> sin(x) = tan(x) / sqrt(&1 + tan(x) pow 2)`;;

(* ------------------------------------------------------------------------- *)
(* Monotonicity theorems for the basic trig functions.                       *)
(* ------------------------------------------------------------------------- *)

let SIN_MONO_LT = `!x y. --(pi / &2) <= x /\ x < y /\ y <= pi / &2 ==> sin(x) < sin(y)`;;

let SIN_MONO_LE = `!x y. --(pi / &2) <= x /\ x <= y /\ y <= pi / &2 ==> sin(x) <= sin(y)`;;

let SIN_MONO_LT_EQ = `!x y. --(pi / &2) <= x /\ x <= pi / &2 /\ --(pi / &2) <= y /\ y <= pi / &2
         ==> (sin(x) < sin(y) <=> x < y)`;;

let SIN_MONO_LE_EQ = `!x y. --(pi / &2) <= x /\ x <= pi / &2 /\ --(pi / &2) <= y /\ y <= pi / &2
         ==> (sin(x) <= sin(y) <=> x <= y)`;;

let SIN_INJ_PI = `!x y. --(pi / &2) <= x /\ x <= pi / &2 /\
         --(pi / &2) <= y /\ y <= pi / &2 /\
         sin(x) = sin(y)
         ==> x = y`;;

let COS_MONO_LT = `!x y. &0 <= x /\ x < y /\ y <= pi ==> cos(y) < cos(x)`;;

let COS_MONO_LE = `!x y. &0 <= x /\ x <= y /\ y <= pi ==> cos(y) <= cos(x)`;;

let COS_MONO_LT_EQ = `!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi
         ==> (cos(x) < cos(y) <=> y < x)`;;

let COS_MONO_LE_EQ = `!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi
         ==> (cos(x) <= cos(y) <=> y <= x)`;;

let COS_INJ_PI = `!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi /\ cos(x) = cos(y)
         ==> x = y`;;

let REAL_ABS_COS_MONO_LE_EQ = `!x y. abs(x) <= pi / &2 /\ abs(y) <= pi / &2
         ==> (abs(cos x) <= abs(cos y) <=> abs y <= abs x)`;;

let TAN_MONO_LT = `!x y. --(pi / &2) < x /\ x < y /\ y < pi / &2 ==> tan(x) < tan(y)`;;

let TAN_MONO_LE = `!x y. --(pi / &2) < x /\ x <= y /\ y < pi / &2 ==> tan(x) <= tan(y)`;;

let TAN_MONO_LT_EQ = `!x y. --(pi / &2) < x /\ x < pi / &2 /\ --(pi / &2) < y /\ y < pi / &2
         ==> (tan(x) < tan(y) <=> x < y)`;;

let TAN_MONO_LE_EQ = `!x y. --(pi / &2) < x /\ x < pi / &2 /\ --(pi / &2) < y /\ y < pi / &2
         ==> (tan(x) <= tan(y) <=> x <= y)`;;

let TAN_BOUND_PI2 = `!x. abs(x) < pi / &4 ==> abs(tan x) < &1`;;

let TAN_COT = `!x. tan(pi / &2 - x) = inv(tan x)`;;

let REAL_ABS_SIN_BOUND_LT = `!x. ~(x = &0) ==> abs(sin x) < abs x`;;

let REAL_ABS_SIN_BOUND_LE = `!x. abs(sin x) <= abs x`;;

(* ------------------------------------------------------------------------- *)
(* Approximation to pi.                                                      *)
(* ------------------------------------------------------------------------- *)

let SIN_PI6_STRADDLE = `!a b. &0 <= a /\ a <= b /\ b <= &4 /\
         sin(a / &6) <= &1 / &2 /\ &1 / &2 <= sin(b / &6)
         ==> a <= pi /\ pi <= b`;;

let PI_APPROX_32 = `abs(pi - &13493037705 / &4294967296) <= inv(&2 pow 32)`;;

let PI2_BOUNDS = `&0 < pi / &2 /\ pi / &2 < &2`;;

(* ------------------------------------------------------------------------- *)
(* Complex logarithms (the conventional principal value).                    *)
(* ------------------------------------------------------------------------- *)

let clog = new_definition
 `clog z = @w. cexp(w) = z /\ --pi < Im(w) /\ Im(w) <= pi`;;

let EXISTS_COMPLEX' = `!P. (?z. P (Re z) (Im z)) <=> ?x y. P x y`;;

let CLOG_WORKS = `!z. ~(z = Cx(&0))
       ==> cexp(clog z) = z /\ --pi < Im(clog z) /\ Im(clog z) <= pi`;;

let CEXP_CLOG = `!z. ~(z = Cx(&0)) ==> cexp(clog z) = z`;;

let CLOG_CEXP = `!z. --pi < Im(z) /\ Im(z) <= pi ==> clog(cexp z) = z`;;

let CLOG_EQ = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) ==> (clog w = clog z <=> w = z)`;;

let CLOG_UNIQUE = `!w z. --pi < Im(z) /\ Im(z) <= pi /\ cexp(z) = w ==> clog w = z`;;

let RE_CLOG = `!z. ~(z = Cx(&0)) ==> Re(clog z) = log(norm z)`;;

let EXISTS_COMPLEX_ROOT = `!a n. ~(n = 0) ==> ?z. z pow n = a`;;

(* ------------------------------------------------------------------------- *)
(* Derivative of clog away from the branch cut.                              *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_CLOG = `!z. (Im(z) = &0 ==> &0 < Re(z))
       ==> (clog has_complex_derivative inv(z)) (at z)`;;

let COMPLEX_DIFFERENTIABLE_AT_CLOG = `!z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_CLOG = `!s z. (Im(z) = &0 ==> &0 < Re(z))
         ==> clog complex_differentiable (at z within s)`;;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CLOG)));;

let CONTINUOUS_AT_CLOG = `!z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous at z`;;

let CONTINUOUS_WITHIN_CLOG = `!s z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous (at z within s)`;;

let CONTINUOUS_ON_CLOG = `!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous_on s`;;

let HOLOMORPHIC_ON_CLOG = `!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> clog holomorphic_on s`;;

(* ------------------------------------------------------------------------- *)
(* Relation to real log.                                                     *)
(* ------------------------------------------------------------------------- *)

let CX_LOG = `!z. &0 < z ==> Cx(log z) = clog(Cx z)`;;

(* ------------------------------------------------------------------------- *)
(* Quadrant-type results for clog.                                           *)
(* ------------------------------------------------------------------------- *)

let RE_CLOG_POS_LT = `!z. ~(z = Cx(&0)) ==> (abs(Im(clog z)) < pi / &2 <=> &0 < Re(z))`;;

let RE_CLOG_POS_LE = `!z. ~(z = Cx(&0)) ==> (abs(Im(clog z)) <= pi / &2 <=> &0 <= Re(z))`;;

let IM_CLOG_POS_LT = `!z. ~(z = Cx(&0)) ==> (&0 < Im(clog z) /\ Im(clog z) < pi <=> &0 < Im(z))`;;

let IM_CLOG_POS_LE = `!z. ~(z = Cx(&0)) ==> (&0 <= Im(clog z) <=> &0 <= Im(z))`;;

let RE_CLOG_POS_LT_IMP = `!z. &0 < Re(z) ==> abs(Im(clog z)) < pi / &2`;;

let IM_CLOG_POS_LT_IMP = `!z. &0 < Im(z) ==> &0 < Im(clog z) /\ Im(clog z) < pi`;;

let IM_CLOG_EQ_0 = `!z. ~(z = Cx(&0)) ==> (Im(clog z) = &0 <=> &0 < Re(z) /\ Im(z) = &0)`;;

let IM_CLOG_EQ_PI = `!z. ~(z = Cx(&0)) ==> (Im(clog z) = pi <=> Re(z) < &0 /\ Im(z) = &0)`;;

(* ------------------------------------------------------------------------- *)
(* Various properties.                                                       *)
(* ------------------------------------------------------------------------- *)

let CNJ_CLOG = `!z. (Im z = &0 ==> &0 < Re z) ==> cnj(clog z) = clog(cnj z)`;;

let CLOG_INV = `!z. (Im(z) = &0 ==> &0 < Re z) ==> clog(inv z) = --(clog z)`;;

let CLOG_1 = `clog(Cx(&1)) = Cx(&0)`;;

let CLOG_NEG_1 = `clog(--Cx(&1)) = ii * Cx pi`;;

let CLOG_II = `clog ii = ii * Cx(pi / &2)`;;

let CLOG_NEG_II = `clog(--ii) = --ii * Cx(pi / &2)`;;

(* ------------------------------------------------------------------------- *)
(* Relation between square root and exp/log, and hence its derivative.       *)
(* ------------------------------------------------------------------------- *)

let CSQRT_CEXP_CLOG = `!z. ~(z = Cx(&0)) ==> csqrt z = cexp(clog(z) / Cx(&2))`;;

let CNJ_CSQRT = `!z. (Im z = &0 ==> &0 <= Re(z)) ==> cnj(csqrt z) = csqrt(cnj z)`;;

let HAS_COMPLEX_DERIVATIVE_CSQRT = `!z. (Im z = &0 ==> &0 < Re(z))
       ==> (csqrt has_complex_derivative inv(Cx(&2) * csqrt z)) (at z)`;;

let COMPLEX_DIFFERENTIABLE_AT_CSQRT = `!z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_CSQRT = `!s z. (Im z = &0 ==> &0 < Re(z))
         ==> csqrt complex_differentiable (at z within s)`;;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CSQRT)));;

let CONTINUOUS_AT_CSQRT = `!z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous at z`;;

let CONTINUOUS_WITHIN_CSQRT = `!s z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous (at z within s)`;;

let CONTINUOUS_ON_CSQRT = `!s. (!z. z IN s /\ Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous_on s`;;

let HOLOMORPHIC_ON_CSQRT = `!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> csqrt holomorphic_on s`;;

let CONTINUOUS_WITHIN_CSQRT_POSREAL = `!z. csqrt continuous (at z within {w | real w /\ &0 <= Re(w)})`;;

(* ------------------------------------------------------------------------- *)
(* Complex powers.                                                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("cpow",(24,"left"));;

let cpow = new_definition
 `w cpow z = if w = Cx(&0) then Cx(&0)
             else cexp(z * clog w)`;;

let CPOW_0 = `!z. Cx(&0) cpow z = Cx(&0)`;;

let CPOW_N = `!z. z cpow (Cx(&n)) = if z = Cx(&0) then Cx(&0) else z pow n`;;

let CPOW_1 = `!z. Cx(&1) cpow z = Cx(&1)`;;

let CPOW_ADD = `!w z1 z2. w cpow (z1 + z2) = w cpow z1 * w cpow z2`;;

let CPOW_SUC = `!w z. w cpow (z + Cx(&1)) = w * w cpow z`;;

let CPOW_NEG = `!w z. w cpow (--z) = inv(w cpow z)`;;

let CPOW_SUB = `!w z1 z2. w cpow (z1 - z2) = w cpow z1 / w cpow z2`;;

let CEXP_MUL_CPOW = `!w z. --pi < Im w /\ Im w <= pi ==> cexp(w * z) = cexp(w) cpow z`;;

let CPOW_EQ_0 = `!w z. w cpow z = Cx(&0) <=> w = Cx(&0)`;;

let NORM_CPOW_REAL = `!w z. real w /\ &0 < Re w ==> norm(w cpow z) = exp(Re z * log(Re w))`;;

let CPOW_REAL_REAL = `!w z. real w /\ real z /\ &0 < Re w
         ==> w cpow z = Cx(exp(Re z * log(Re w)))`;;

let NORM_CPOW_REAL_MONO = `!w z1 z2. real w /\ &1 < Re w
             ==> (norm(w cpow z1) <= norm(w cpow z2) <=> Re(z1) <= Re(z2))`;;

let CPOW_MUL_REAL = `!x y z. real x /\ real y /\ &0 <= Re x /\ &0 <= Re y
           ==> (x * y) cpow z = x cpow z * y cpow z`;;

let HAS_COMPLEX_DERIVATIVE_CPOW = `!s z. (Im z = &0 ==> &0 < Re z)
         ==> ((\z. z cpow s) has_complex_derivative
              (s * z cpow (s - Cx(&1)))) (at z)`;;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (GEN `s:complex`
     (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               (SPEC `s:complex` HAS_COMPLEX_DERIVATIVE_CPOW)))));;

let HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT = `!w z. ~(w = Cx(&0))
         ==> ((\z. w cpow z) has_complex_derivative clog(w) * w cpow z) (at z)`;;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (GEN `s:complex`
     (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               (SPEC `s:complex` HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT)))));;

let COMPLEX_DIFFERENTIABLE_CPOW_RIGHT = `!w z. (\z. w cpow z) complex_differentiable (at z)`;;

let HOLOMORPHIC_ON_CPOW_RIGHT = `!w f s. f holomorphic_on s
           ==> (\z. w cpow (f z)) holomorphic_on s`;;

let CONTINUOUS_ON_CPOW_RIGHT = `!w f s. f continuous_on s
           ==> (\z. w cpow (f z)) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Product rule.                                                             *)
(* ------------------------------------------------------------------------- *)

let CLOG_MUL = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
           ==> clog(w * z) =
                if Im(clog w + clog z) <= --pi then
                  (clog(w) + clog(z)) + ii * Cx(&2 * pi)
                else if Im(clog w + clog z) > pi then
                  (clog(w) + clog(z)) - ii * Cx(&2 * pi)
                else clog(w) + clog(z)`;;

let CLOG_MUL_SIMPLE = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) /\
         --pi < Im(clog(w)) + Im(clog(z)) /\
         Im(clog(w)) + Im(clog(z)) <= pi
         ==> clog(w * z) = clog(w) + clog(z)`;;

let CLOG_MUL_CX = `(!x z. &0 < x /\ ~(z = Cx(&0)) ==> clog(Cx x * z) = Cx(log x) + clog z) /\
   (!x z. &0 < x /\ ~(z = Cx(&0)) ==> clog(z * Cx x) = clog z + Cx(log x))`;;

let CLOG_MUL_POS = `!w z. &0 < Re w /\ &0 < Re z ==> clog(w * z) = clog w + clog z`;;

let CLOG_DIV_POS = `!w z. &0 < Re w /\ &0 < Re z ==> clog(w / z) = clog w - clog z`;;

let CLOG_NEG = `!z. ~(z = Cx(&0))
       ==> clog(--z) = if Im(z) <= &0 /\ ~(Re(z) < &0 /\ Im(z) = &0)
                       then clog(z) + ii * Cx(pi)
                       else clog(z) - ii * Cx(pi)`;;

let CLOG_MUL_II = `!z. ~(z = Cx(&0))
       ==> clog(ii * z) = if &0 <= Re(z) \/ Im(z) < &0
                          then clog(z) + ii * Cx(pi / &2)
                          else clog(z) - ii * Cx(&3 * pi / &2)`;;

(* ------------------------------------------------------------------------- *)
(* Unwinding number gives another version of log-product formula.            *)
(* Note that in this special case the unwinding number is -1, 0 or 1.        *)
(* ------------------------------------------------------------------------- *)

let unwinding = new_definition
 `unwinding(z) = (z - clog(cexp z)) / (Cx(&2 * pi) * ii)`;;

let UNWINDING_2PI = `Cx(&2 * pi) * ii * unwinding(z) = z - clog(cexp z)`;;

let CLOG_MUL_UNWINDING = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
           ==> clog(w * z) =
               clog(w) + clog(z) -
               Cx(&2 * pi) * ii * unwinding(clog w + clog z)`;;

(* ------------------------------------------------------------------------- *)
(* Complex arctangent (branch cut gives standard bounds in real case).       *)
(* ------------------------------------------------------------------------- *)

let catn = new_definition
 `catn z = (ii / Cx(&2)) * clog((Cx(&1) - ii * z) / (Cx(&1) + ii * z))`;;

let CATN_0 = `catn(Cx(&0)) = Cx(&0)`;;

let IM_COMPLEX_DIV_LEMMA = `!z. Im((Cx(&1) - ii * z) / (Cx(&1) + ii * z)) = &0 <=> Re z = &0`;;

let RE_COMPLEX_DIV_LEMMA = `!z. &0 < Re((Cx(&1) - ii * z) / (Cx(&1) + ii * z)) <=> norm(z) < &1`;;

let CTAN_CATN = `!z. ~(z pow 2 = --Cx(&1)) ==> ctan(catn z) = z`;;

let CATN_CTAN = `!z. abs(Re z) < pi / &2 ==> catn(ctan z) = z`;;

let RE_CATN_BOUNDS = `!z. (Re z = &0 ==> abs(Im z) < &1) ==> abs(Re(catn z)) < pi / &2`;;

let HAS_COMPLEX_DERIVATIVE_CATN = `!z. (Re z = &0 ==> abs(Im z) < &1)
       ==> (catn has_complex_derivative inv(Cx(&1) + z pow 2)) (at z)`;;

let COMPLEX_DIFFERENTIABLE_AT_CATN = `!z. (Re z = &0 ==> abs(Im z) < &1) ==> catn complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_CATN = `!s z. (Re z = &0 ==> abs(Im z) < &1)
         ==> catn complex_differentiable (at z within s)`;;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CATN)));;

let CONTINUOUS_AT_CATN = `!z. (Re z = &0 ==> abs(Im z) < &1) ==> catn continuous at z`;;

let CONTINUOUS_WITHIN_CATN = `!s z. (Re z = &0 ==> abs(Im z) < &1) ==> catn continuous (at z within s)`;;

let CONTINUOUS_ON_CATN = `!s. (!z. z IN s /\ Re z = &0 ==> abs(Im z) < &1) ==> catn continuous_on s`;;

let HOLOMORPHIC_ON_CATN = `!s. (!z. z IN s /\ Re z = &0 ==> abs(Im z) < &1) ==> catn holomorphic_on s`;;

(* ------------------------------------------------------------------------- *)
(* Real arctangent.                                                          *)
(* ------------------------------------------------------------------------- *)

let atn = new_definition
 `atn(x) = Re(catn(Cx x))`;;

let CX_ATN = `!x. Cx(atn x) = catn(Cx x)`;;

let ATN_TAN = `!y. tan(atn y) = y`;;

let ATN_BOUND = `!y. abs(atn y) < pi / &2`;;

let ATN_BOUNDS = `!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2)`;;

let TAN_ATN = `!x. --(pi / &2) < x /\ x < pi / &2 ==> atn(tan(x)) = x`;;

let ATN_0 = `atn(&0) = &0`;;

let ATN_1 = `atn(&1) = pi / &4`;;

let ATN_NEG = `!x. atn(--x) = --(atn x)`;;

let ATN_MONO_LT = `!x y. x < y ==> atn(x) < atn(y)`;;

let ATN_MONO_LT_EQ = `!x y. atn(x) < atn(y) <=> x < y`;;

let ATN_MONO_LE_EQ = `!x y. atn(x) <= atn(y) <=> x <= y`;;

let ATN_INJ = `!x y. (atn x = atn y) <=> (x = y)`;;

let ATN_POS_LT = `&0 < atn(x) <=> &0 < x`;;

let ATN_POS_LE = `&0 <= atn(x) <=> &0 <= x`;;

let ATN_LT_PI4_POS = `!x. x < &1 ==> atn(x) < pi / &4`;;

let ATN_LT_PI4_NEG = `!x. --(&1) < x ==> --(pi / &4) < atn(x)`;;

let ATN_LT_PI4 = `!x. abs(x) < &1 ==> abs(atn x) < pi / &4`;;

let ATN_LE_PI4 = `!x. abs(x) <= &1 ==> abs(atn x) <= pi / &4`;;

let COS_ATN_NZ = `!x. ~(cos(atn(x)) = &0)`;;

let TAN_SEC = `!x. ~(cos(x) = &0) ==> (&1 + (tan(x) pow 2) = inv(cos x) pow 2)`;;

let COS_ATN = `!x. cos(atn x) = &1 / sqrt(&1 + x pow 2)`;;

let SIN_ATN = `!x. sin(atn x) = x / sqrt(&1 + x pow 2)`;;

let ATN_ABS = `!x. atn(abs x) = abs(atn x)`;;

let ATN_ADD = `!x y. abs(atn x + atn y) < pi / &2
         ==> atn(x) + atn(y) = atn((x + y) / (&1 - x * y))`;;

let ATN_INV = `!x. &0 < x ==> atn(inv x) = pi / &2 - atn x`;;

let ATN_ADD_SMALL = `!x y. abs(x * y) < &1
         ==> (atn(x) + atn(y) = atn((x + y) / (&1 - x * y)))`;;

(* ------------------------------------------------------------------------- *)
(* Machin-like formulas for pi.                                              *)
(* ------------------------------------------------------------------------- *)

let [MACHIN; MACHIN_EULER; MACHIN_GAUSS] = (CONJUNCTS o prove)
 (`(&4 * atn(&1 / &5) - atn(&1 / &239) = pi / &4) /\
   (&5 * atn(&1 / &7) + &2 * atn(&3 / &79) = pi / &4) /\
   (&12 * atn(&1 / &18) + &8 * atn(&1 / &57) - &5 * atn(&1 / &239) = pi / &4)`,
  REPEAT CONJ_TAC THEN CONV_TAC(ONCE_DEPTH_CONV(fun tm ->
    if is_binop `( * ):real->real->real` tm
    then LAND_CONV(RAND_CONV(TOP_DEPTH_CONV num_CONV)) tm
    else failwith "")) THEN
  REWRITE_TAC[real_sub; GSYM REAL_MUL_RNEG; GSYM ATN_NEG] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_LID] THEN
  CONV_TAC(DEPTH_CONV (fun tm ->
    let th1 = PART_MATCH (lhand o rand) ATN_ADD_SMALL tm in
    let th2 = MP th1 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th1)))) in
    CONV_RULE(RAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) th2)) THEN
  REWRITE_TAC[ATN_1]);;

(* ------------------------------------------------------------------------- *)
(* Some bound theorems where a bit of simple calculus is handy.              *)
(* ------------------------------------------------------------------------- *)

let ATN_ABS_LE_X = `!x. abs(atn x) <= abs x`;;

let ATN_LE_X = `!x. &0 <= x ==> atn(x) <= x`;;

let TAN_ABS_GE_X = `!x. abs(x) < pi / &2 ==> abs(x) <= abs(tan x)`;;

(* ------------------------------------------------------------------------- *)
(* Probably not very useful, but for compatibility with old analysis theory. *)
(* ------------------------------------------------------------------------- *)

let TAN_TOTAL = `!y. ?!x. --(pi / &2) < x /\ x < (pi / &2) /\ tan(x) = y`;;

let TAN_TOTAL_POS = `!y. &0 <= y ==> ?x. &0 <= x /\ x < pi / &2 /\ tan(x) = y`;;

let TAN_TOTAL_LEMMA = `!y. &0 < y ==> ?x. &0 < x /\ x < pi / &2 /\ y < tan(x)`;;

(* ------------------------------------------------------------------------- *)
(* Some slightly ad hoc lemmas useful here.                                  *)
(* ------------------------------------------------------------------------- *)

let RE_POW_2 = `Re(z pow 2) = Re(z) pow 2 - Im(z) pow 2`;;

let IM_POW_2 = `Im(z pow 2) = &2 * Re(z) * Im(z)`;;

(* ------------------------------------------------------------------------- *)
(* Inverse sine.                                                             *)
(* ------------------------------------------------------------------------- *)

let casn = new_definition
 `casn z = --ii * clog(ii * z + csqrt(Cx(&1) - z pow 2))`;;

let CASN_BODY_LEMMA = `!z. ~(ii * z + csqrt(Cx(&1) - z pow 2) = Cx(&0))`;;

let CSIN_CASN = `!z. csin(casn z) = z`;;

let CASN_CSIN = `!z. abs(Re z) < pi / &2 \/ (abs(Re z) = pi / &2 /\ Im z = &0)
       ==> casn(csin z) = z`;;

let CASN_UNIQUE = `!w z. csin(z) = w /\
         (abs(Re z) < pi / &2 \/ (abs(Re z) = pi / &2 /\ Im z = &0))
         ==> casn w = z`;;

let CASN_0 = `casn(Cx(&0)) = Cx(&0)`;;

let CASN_1 = `casn(Cx(&1)) = Cx(pi / &2)`;;

let CASN_NEG_1 = `casn(--Cx(&1)) = --Cx(pi / &2)`;;

let HAS_COMPLEX_DERIVATIVE_CASN = `!z. (Im z = &0 ==> abs(Re z) < &1)
       ==> (casn has_complex_derivative inv(ccos(casn z))) (at z)`;;

let COMPLEX_DIFFERENTIABLE_AT_CASN = `!z. (Im z = &0 ==> abs(Re z) < &1) ==> casn complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_CASN = `!s z. (Im z = &0 ==> abs(Re z) < &1)
         ==> casn complex_differentiable (at z within s)`;;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CASN)));;

let CONTINUOUS_AT_CASN = `!z. (Im z = &0 ==> abs(Re z) < &1) ==> casn continuous at z`;;

let CONTINUOUS_WITHIN_CASN = `!s z. (Im z = &0 ==> abs(Re z) < &1) ==> casn continuous (at z within s)`;;

let CONTINUOUS_ON_CASN = `!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> casn continuous_on s`;;

let HOLOMORPHIC_ON_CASN = `!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> casn holomorphic_on s`;;

(* ------------------------------------------------------------------------- *)
(* Inverse cosine.                                                           *)
(* ------------------------------------------------------------------------- *)

let cacs = new_definition
 `cacs z = --ii * clog(z + ii * csqrt(Cx(&1) - z pow 2))`;;

let CACS_BODY_LEMMA = `!z. ~(z + ii * csqrt(Cx(&1) - z pow 2) = Cx(&0))`;;

let CCOS_CACS = `!z. ccos(cacs z) = z`;;

let CACS_CCOS = `!z. &0 < Re z /\ Re z < pi \/
       Re(z) = &0 /\ &0 <= Im(z) \/
       Re(z) = pi /\ Im(z) <= &0
       ==> cacs(ccos z) = z`;;

let CACS_UNIQUE = `!w z.
       ccos z = w /\
       (&0 < Re z /\ Re z < pi \/
        Re(z) = &0 /\ &0 <= Im(z) \/
        Re(z) = pi /\ Im(z) <= &0)
       ==> cacs(w) = z`;;

let CACS_0 = `cacs(Cx(&0)) = Cx(pi / &2)`;;

let CACS_1 = `cacs(Cx(&1)) = Cx(&0)`;;

let CACS_NEG_1 = `cacs(--Cx(&1)) = Cx pi`;;

let HAS_COMPLEX_DERIVATIVE_CACS = `!z. (Im z = &0 ==> abs(Re z) < &1)
       ==> (cacs has_complex_derivative --inv(csin(cacs z))) (at z)`;;

let COMPLEX_DIFFERENTIABLE_AT_CACS = `!z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_CACS = `!s z. (Im z = &0 ==> abs(Re z) < &1)
         ==> cacs complex_differentiable (at z within s)`;;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CACS)));;

let CONTINUOUS_AT_CACS = `!z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous at z`;;

let CONTINUOUS_WITHIN_CACS = `!s z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous (at z within s)`;;

let CONTINUOUS_ON_CACS = `!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous_on s`;;

let HOLOMORPHIC_ON_CACS = `!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> cacs holomorphic_on s`;;

(* ------------------------------------------------------------------------- *)
(* Some crude range theorems (could be sharpened).                           *)
(* ------------------------------------------------------------------------- *)

let CASN_RANGE_LEMMA = `!z. abs (Re z) < &1 ==> &0 < Re(ii * z + csqrt(Cx(&1) - z pow 2))`;;

let CACS_RANGE_LEMMA = `!z. abs(Re z) < &1 ==> &0 < Im(z + ii * csqrt(Cx(&1) - z pow 2))`;;

let RE_CASN = `!z. Re(casn z) = Im(clog(ii * z + csqrt(Cx(&1) - z pow 2)))`;;

let RE_CACS = `!z. Re(cacs z) = Im(clog(z + ii * csqrt(Cx(&1) - z pow 2)))`;;

let CASN_BOUNDS = `!z. abs(Re z) < &1 ==> abs(Re(casn z)) < pi / &2`;;

let CACS_BOUNDS = `!z. abs(Re z) < &1 ==> &0 < Re(cacs z) /\ Re(cacs z) < pi`;;

let RE_CACS_BOUNDS = `!z. --pi < Re(cacs z) /\ Re(cacs z) <= pi`;;

let RE_CACS_BOUND = `!z. abs(Re(cacs z)) <= pi`;;

let RE_CASN_BOUNDS = `!z. --pi < Re(casn z) /\ Re(casn z) <= pi`;;

let RE_CASN_BOUND = `!z. abs(Re(casn z)) <= pi`;;

(* ------------------------------------------------------------------------- *)
(* Interrelations between the two functions.                                 *)
(* ------------------------------------------------------------------------- *)

let CCOS_CASN_NZ = `!z. ~(z pow 2 = Cx(&1)) ==> ~(ccos(casn z) = Cx(&0))`;;

let CSIN_CACS_NZ = `!z. ~(z pow 2 = Cx(&1)) ==> ~(csin(cacs z) = Cx(&0))`;;

let CCOS_CSIN_CSQRT = `!z. &0 < cos(Re z) \/ cos(Re z) = &0 /\ Im(z) * sin(Re z) <= &0
       ==> ccos(z) = csqrt(Cx(&1) - csin(z) pow 2)`;;

let CSIN_CCOS_CSQRT = `!z. &0 < sin(Re z) \/ sin(Re z) = &0 /\ &0 <= Im(z) * cos(Re z)
       ==> csin(z) = csqrt(Cx(&1) - ccos(z) pow 2)`;;

let CASN_CACS_SQRT_POS = `!z. (&0 < Re z \/ Re z = &0 /\ &0 <= Im z)
       ==> casn(z) = cacs(csqrt(Cx(&1) - z pow 2))`;;

let CACS_CASN_SQRT_POS = `!z. (&0 < Re z \/ Re z = &0 /\ &0 <= Im z)
       ==> cacs(z) = casn(csqrt(Cx(&1) - z pow 2))`;;

let CSIN_CACS = `!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im z
       ==> csin(cacs z) = csqrt(Cx(&1) - z pow 2)`;;

let CCOS_CASN = `!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im z
       ==> ccos(casn z) = csqrt(Cx(&1) - z pow 2)`;;

(* ------------------------------------------------------------------------- *)
(* Real arcsin.                                                              *)
(* ------------------------------------------------------------------------- *)

let asn = new_definition `asn(x) = Re(casn(Cx x))`;;

let REAL_ASN = `!z. real z /\ abs(Re z) <= &1 ==> real(casn z)`;;

let CX_ASN = `!x. abs(x) <= &1 ==> Cx(asn x) = casn(Cx x)`;;

let SIN_ASN = `!y. --(&1) <= y /\ y <= &1 ==> sin(asn(y)) = y`;;

let ASN_SIN = `!x. --(pi / &2) <= x /\ x <= pi / &2 ==> asn(sin(x)) = x`;;

let ASN_BOUNDS_LT = `!y. --(&1) < y /\ y < &1 ==> --(pi / &2) < asn(y) /\ asn(y) < pi / &2`;;

let ASN_0 = `asn(&0) = &0`;;

let ASN_1 = `asn(&1) = pi / &2`;;

let ASN_NEG_1 = `asn(-- &1) = --(pi / &2)`;;

let ASN_BOUNDS = `!y. --(&1) <= y /\ y <= &1 ==> --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2`;;

let ASN_BOUNDS_PI2 = `!x. &0 <= x /\ x <= &1 ==> &0 <= asn x /\ asn x <= pi / &2`;;

let ASN_NEG = `!x. -- &1 <= x /\ x <= &1 ==> asn(--x) = --asn(x)`;;

let COS_ASN_NZ = `!x. --(&1) < x /\ x < &1 ==> ~(cos(asn(x)) = &0)`;;

let ASN_MONO_LT_EQ = `!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (asn(x) < asn(y) <=> x < y)`;;

let ASN_MONO_LE_EQ = `!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (asn(x) <= asn(y) <=> x <= y)`;;

let ASN_MONO_LT = `!x y. --(&1) <= x /\ x < y /\ y <= &1 ==> asn(x) < asn(y)`;;

let ASN_MONO_LE = `!x y. --(&1) <= x /\ x <= y /\ y <= &1 ==> asn(x) <= asn(y)`;;

let COS_ASN = `!x. --(&1) <= x /\ x <= &1 ==> cos(asn x) = sqrt(&1 - x pow 2)`;;

(* ------------------------------------------------------------------------- *)
(* Real arccosine.                                                           *)
(* ------------------------------------------------------------------------- *)

let acs = new_definition `acs(x) = Re(cacs(Cx x))`;;

let REAL_ACS = `!z. real z /\ abs(Re z) <= &1 ==> real(cacs z)`;;

let CX_ACS = `!x. abs(x) <= &1 ==> Cx(acs x) = cacs(Cx x)`;;

let COS_ACS = `!y. --(&1) <= y /\ y <= &1 ==> cos(acs(y)) = y`;;

let ACS_COS = `!x. &0 <= x /\ x <= pi ==> acs(cos(x)) = x`;;

let ACS_BOUNDS_LT = `!y. --(&1) < y /\ y < &1 ==> &0 < acs(y) /\ acs(y) < pi`;;

let ACS_0 = `acs(&0) = pi / &2`;;

let ACS_1 = `acs(&1) = &0`;;

let ACS_NEG_1 = `acs(-- &1) = pi`;;

let ACS_BOUNDS = `!y. --(&1) <= y /\ y <= &1 ==> &0 <= acs(y) /\ acs(y) <= pi`;;

let ACS_NEG = `!x. -- &1 <= x /\ x <= &1 ==> acs(--x) = pi - acs(x)`;;

let SIN_ACS_NZ = `!x. --(&1) < x /\ x < &1 ==> ~(sin(acs(x)) = &0)`;;

let ACS_MONO_LT_EQ = `!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs(x) < acs(y) <=> y < x)`;;

let ACS_MONO_LE_EQ = `!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs(x) <= acs(y) <=> y <= x)`;;

let ACS_MONO_LT = `!x y. --(&1) <= x /\ x < y /\ y <= &1 ==> acs(y) < acs(x)`;;

let ACS_MONO_LE = `!x y. --(&1) <= x /\ x <= y /\ y <= &1 ==> acs(y) <= acs(x)`;;

let SIN_ACS = `!x. --(&1) <= x /\ x <= &1 ==> sin(acs x) = sqrt(&1 - x pow 2)`;;

let ACS_INJ = `!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs x = acs y <=> x = y)`;;

(* ------------------------------------------------------------------------- *)
(* Some interrelationships among the real inverse trig functions.            *)
(* ------------------------------------------------------------------------- *)

let ACS_ATN = `!x. -- &1 < x /\ x < &1 ==> acs(x) = pi / &2 - atn(x / sqrt(&1 - x pow 2))`;;

let ASN_PLUS_ACS = `!x. -- &1 <= x /\ x <= &1 ==> asn(x) + acs(x) = pi / &2`;;

let ASN_ACS = `!x. -- &1 <= x /\ x <= &1 ==> asn(x) = pi / &2 - acs(x)`;;

let ACS_ASN = `!x. -- &1 <= x /\ x <= &1 ==> acs(x) = pi / &2 - asn(x)`;;

let ASN_ATN = `!x. -- &1 < x /\ x < &1 ==> asn(x) = atn(x / sqrt(&1 - x pow 2))`;;

let ASN_ACS_SQRT_POS = `!x. &0 <= x /\ x <= &1 ==> asn(x) = acs(sqrt(&1 - x pow 2))`;;

let ASN_ACS_SQRT_NEG = `!x. -- &1 <= x /\ x <= &0 ==> asn(x) = --acs(sqrt(&1 - x pow 2))`;;

let ACS_ASN_SQRT_POS = `!x. &0 <= x /\ x <= &1 ==> acs(x) = asn(sqrt(&1 - x pow 2))`;;

let ACS_ASN_SQRT_NEG = `!x. -- &1 <= x /\ x <= &0 ==> acs(x) = pi - asn(sqrt(&1 - x pow 2))`;;

(* ------------------------------------------------------------------------- *)
(* More delicate continuity results for arcsin and arccos.                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CASN_REAL = `casn continuous_on {w | real w /\ abs(Re w) <= &1}`;;

let CONTINUOUS_WITHIN_CASN_REAL = `!z. casn continuous (at z within {w | real w /\ abs(Re w) <= &1})`;;

let CONTINUOUS_ON_CACS_REAL = `cacs continuous_on {w | real w /\ abs(Re w) <= &1}`;;

let CONTINUOUS_WITHIN_CACS_REAL = `!z. cacs continuous (at z within {w | real w /\ abs(Re w) <= &1})`;;

(* ------------------------------------------------------------------------- *)
(* Some limits, most involving sequences of transcendentals.                 *)
(* ------------------------------------------------------------------------- *)

let LIM_CX_OVER_CEXP = `((\x. Cx x / cexp(Cx x)) --> Cx(&0)) at_posinfinity`;;

let LIM_Z_TIMES_CLOG = `((\z. z * clog z) --> Cx(&0)) (at (Cx(&0)))`;;

let LIM_LOG_OVER_Z = `((\z. clog z / z) --> Cx(&0)) at_infinity`;;

let LIM_LOG_OVER_POWER = `!s. &0 < Re s
       ==> ((\x. clog(Cx x) / (Cx x) cpow s) --> Cx(&0)) at_posinfinity`;;

let LIM_LOG_OVER_X = `((\x. clog(Cx x) / Cx x) --> Cx(&0)) at_posinfinity`;;

let LIM_LOG_OVER_POWER_N = `!s. &0 < Re s
       ==> ((\n. clog(Cx(&n)) / Cx(&n) cpow s) --> Cx(&0)) sequentially`;;

let LIM_LOG_OVER_N = `((\n. clog(Cx(&n)) / Cx(&n)) --> Cx(&0)) sequentially`;;

let LIM_1_OVER_POWER = `!s. &0 < Re s
       ==> ((\n. Cx(&1) / Cx(&n) cpow s) --> Cx(&0)) sequentially`;;

let LIM_INV_Z_OFFSET = `!z. ((\w. inv(w + z)) --> Cx(&0)) at_infinity`;;

let LIM_INV_Z = `((\z. inv(z)) --> Cx(&0)) at_infinity`;;

let LIM_INV_X_OFFSET = `!z. ((\x. inv(Cx x + z)) --> Cx(&0)) at_posinfinity`;;

let LIM_INV_X = `((\x. inv(Cx x)) --> Cx(&0)) at_posinfinity`;;

let LIM_INV_N_OFFSET = `!z. ((\n. inv(Cx(&n) + z)) --> Cx(&0)) sequentially`;;

let LIM_1_OVER_N = `((\n. Cx(&1) / Cx(&n)) --> Cx(&0)) sequentially`;;

let LIM_INV_N = `((\n. inv(Cx(&n))) --> Cx(&0)) sequentially`;;

let LIM_INV_Z_POW_OFFSET = `!z n. 1 <= n ==> ((\w. inv(w + z) pow n) --> Cx(&0)) at_infinity`;;

let LIM_INV_Z_POW = `!n. 1 <= n ==> ((\z. inv(z) pow n) --> Cx(&0)) at_infinity`;;

let LIM_INV_X_POW_OFFSET = `!z n. 1 <= n ==> ((\x. inv(Cx x + z) pow n) --> Cx(&0)) at_posinfinity`;;

let LIM_INV_X_POW = `!n. 1 <= n ==> ((\x. inv(Cx x) pow n) --> Cx(&0)) at_posinfinity`;;

let LIM_INV_N_POW_OFFSET = `!z m. 1 <= m ==> ((\n. inv(Cx(&n) + z) pow m) --> Cx(&0)) sequentially`;;

let LIM_INV_N_POW = `!m. 1 <= m ==> ((\n. inv(Cx(&n)) pow m) --> Cx(&0)) sequentially`;;

let LIM_1_OVER_LOG = `((\n. Cx(&1) / clog(Cx(&n))) --> Cx(&0)) sequentially`;;

let LIM_N_TIMES_POWN = `!z. norm(z) < &1 ==> ((\n. Cx(&n) * z pow n) --> Cx(&0)) sequentially`;;

let LIM_N_OVER_POWN = `!z. &1 < norm(z) ==> ((\n. Cx(&n) / z pow n) --> Cx(&0)) sequentially`;;

let LIM_POWN = `!z. norm(z) < &1 ==> ((\n. z pow n) --> Cx(&0)) sequentially`;;

let LIM_CSIN_OVER_X = `((\z. csin z / z) --> Cx(&1)) (at (Cx(&0)))`;;

(* ------------------------------------------------------------------------- *)
(* Roots of unity.                                                           *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_ROOT_POLYFUN = `!n z a.
        1 <= n
        ==> (z pow n = a <=>
             vsum(0..n) (\i. (if i = 0 then --a else if i = n then Cx(&1)
                              else Cx(&0)) * z pow i) = Cx(&0))`;;

let COMPLEX_ROOT_UNITY = `!n j. ~(n = 0)
         ==> cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) pow n = Cx(&1)`;;

let COMPLEX_ROOT_UNITY_EQ = `!n j k. ~(n = 0)
           ==> (cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) =
                cexp(Cx(&2) * Cx pi * ii * Cx(&k / &n)) <=> (j == k) (mod n))`;;

let COMPLEX_ROOT_UNITY_EQ_1 = `!n j. ~(n = 0)
         ==> (cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) = Cx(&1) <=>
              n divides j)`;;

let FINITE_CARD_COMPLEX_ROOTS_UNITY = `!n. 1 <= n
       ==> FINITE {z | z pow n = Cx(&1)} /\ CARD {z | z pow n = Cx(&1)} <= n`;;

let FINITE_COMPLEX_ROOTS_UNITY = `!n. ~(n = 0) ==> FINITE {z | z pow n = Cx(&1)}`;;

let FINITE_CARD_COMPLEX_ROOTS_UNITY_EXPLICIT = `!n. 1 <= n
       ==> FINITE {cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) | j | j < n} /\
           CARD {cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) | j | j < n} = n`;;

let COMPLEX_ROOTS_UNITY = `!n. 1 <= n
       ==> {z | z pow n = Cx(&1)} =
           {cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) | j | j < n}`;;

let CARD_COMPLEX_ROOTS_UNITY = `!n. 1 <= n ==> CARD {z | z pow n = Cx(&1)} = n`;;

let HAS_SIZE_COMPLEX_ROOTS_UNITY = `!n. 1 <= n ==> {z | z pow n = Cx(&1)} HAS_SIZE n`;;

let COMPLEX_NOT_ROOT_UNITY = `!n. 1 <= n ==> ?u. norm u = &1 /\ ~(u pow n = Cx(&1))`;;

(* ------------------------------------------------------------------------- *)
(* Relation between clog and Arg, and hence continuity of Arg.               *)
(* ------------------------------------------------------------------------- *)

let ARG_CLOG = `!z. &0 < Arg z ==> Arg z = Im(clog(--z)) + pi`;;

let CONTINUOUS_AT_ARG = `!z. ~(real z /\ &0 <= Re z) ==> (Cx o Arg) continuous (at z)`;;

let CONTINUOUS_ON_ARG = `!s. (!z. z IN s /\ real z ==> Re z < &0) ==> (Cx o Arg) continuous_on s`;;

let CONTINUOUS_WITHIN_UPPERHALF_ARG = `!z. ~(z = Cx(&0))
       ==> (Cx o Arg) continuous (at z) within {z | &0 <= Im z}`;;

let CONTINUOUS_ON_UPPERHALF_ARG = `(Cx o Arg) continuous_on ({z | &0 <= Im z} DIFF {Cx(&0)})`;;

let CONTINUOUS_ON_COMPOSE_ARG = `!s p:real->real^N.
        (p o drop) continuous_on interval[vec 0,lift(&2 * pi)] /\
        p(&2 * pi) = p(&0) /\ ~(Cx(&0) IN s)
        ==> (\z. p(Arg z)) continuous_on s`;;

let OPEN_ARG_LTT = `!s t. &0 <= s /\ t <= &2 * pi ==> open {z | s < Arg z /\ Arg z < t}`;;

let OPEN_ARG_GT = `!t. open {z | t < Arg z}`;;

let CLOSED_ARG_LE = `!t. closed {z | Arg z <= t}`;;

(* ------------------------------------------------------------------------- *)
(* Relation between Arg and arctangent in upper halfplane.                   *)
(* ------------------------------------------------------------------------- *)

let ARG_ATAN_UPPERHALF = `!z. &0 < Im z ==> Arg(z) = pi / &2 - atn(Re z / Im z)`;;

(* ------------------------------------------------------------------------- *)
(* Real n'th roots. Regardless of whether n is odd or even, we totalize by   *)
(* setting root_n(-x) = -root_n(x), which makes some convenient facts hold.  *)
(* ------------------------------------------------------------------------- *)

let root = new_definition
 `root(n) x = real_sgn(x) * exp(log(abs x) / &n)`;;

let ROOT_0 = `!n. root n (&0) = &0`;;

let ROOT_1 = `!n. root n (&1) = &1`;;

let ROOT_2 = `!x. root 2 x = sqrt x`;;

let ROOT_NEG = `!n x. root n (--x) = --(root n x)`;;

let ROOT_WORKS = `!n x. real_sgn(root n x) = real_sgn x /\
         (root n x) pow n = if n = 0 then &1
                            else real_sgn(x) pow n * abs x`;;

let REAL_POW_ROOT = `!n x. ODD n \/ ~(n = 0) /\ &0 <= x ==> (root n x) pow n = x`;;

let ROOT_POS_LT = `!n x. &0 < x ==> &0 < root n x`;;

let ROOT_POS_LE = `!n x. &0 <= x ==> &0 <= root n x`;;

let ROOT_LT_0 = `!n x. &0 < root n x <=> &0 < x`;;

let ROOT_LE_0 = `!n x. &0 <= root n x <=> &0 <= x`;;

let ROOT_EQ_0 = `!n x. root n x = &0 <=> x = &0`;;

let REAL_ROOT_MUL = `!n x y. root n (x * y) = root n x * root n y`;;

let REAL_ROOT_POW_GEN = `!m n x. root n (x pow m) = (root n x) pow m`;;

let REAL_ROOT_POW = `!n x. ODD n \/ ~(n = 0) /\ &0 <= x ==> root n (x pow n) = x`;;

let ROOT_UNIQUE = `!n x y. y pow n = x /\ (ODD n \/ ~(n = 0) /\ &0 <= y) ==> root n x = y`;;

let REAL_ROOT_INV = `!n x. root n (inv x) = inv(root n x)`;;

let REAL_ROOT_DIV = `!n x y. root n (x / y) = root n x / root n y`;;

let ROOT_MONO_LT = `!n x y. ~(n = 0) /\ x < y ==> root n x < root n y`;;

let ROOT_MONO_LE = `!n x y. x <= y ==> root n x <= root n y`;;

let ROOT_MONO_LT_EQ = `!n x y. ~(n = 0) ==> (root n x < root n y <=> x < y)`;;

let ROOT_MONO_LE_EQ = `!n x y. ~(n = 0) ==> (root n x <= root n y <=> x <= y)`;;

let ROOT_INJ = `!n x y. ~(n = 0) ==> (root n x = root n y <=> x = y)`;;

let REAL_ROOT_LE = `!n x y. ~(n = 0) /\ &0 <= y
           ==> (root n x <= y <=> x <= y pow n)`;;

let REAL_LE_ROOT = `!n x y. ~(n = 0) /\ &0 <= x
           ==> (x <= root n y <=> x pow n <= y)`;;

let LOG_ROOT = `!n x. ~(n = 0) /\ &0 < x ==> log(root n x) = log x / &n`;;

let ROOT_EXP_LOG = `!n x. ~(n = 0) /\ &0 < x ==> root n x = exp(log x / &n)`;;

let ROOT_PRODUCT = `!n f s. FINITE s ==> root n (product s f) = product s (\i. root n (f i))`;;

let SQRT_PRODUCT = `!f s. FINITE s ==> sqrt(product s f) = product s (\i. sqrt(f i))`;;

(* ------------------------------------------------------------------------- *)
(* Real power function. This involves a few arbitrary choices.               *)
(*                                                                           *)
(* The value of x^y is unarguable when x > 0.                                *)
(*                                                                           *)
(* We make 0^0 = 1 to agree with "pow", but otherwise 0^y = 0.               *)
(*                                                                           *)
(* There is a sensible real value for (-x)^(p/q) where q is odd and either   *)
(* p is even [(-x)^y = x^y] or odd [(-x)^y = -x^y].                          *)
(*                                                                           *)
(* In all other cases, we return (-x)^y = -x^y. This is meaningless but at   *)
(* least it covers half the cases above without another case split.          *)
(*                                                                           *)
(* As for laws of indices, we do have x^-y = 1/x^y. Of course we can't  have *)
(* x^(yz) = x^y^z or x^(y+z) = x^y x^z since then (-1)^(1/2)^2 = -1.         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("rpow",(24,"left"));;

let rpow = new_definition
  `x rpow y = if &0 < x then exp(y * log x)
               else if x = &0 then if y = &0 then &1 else &0
               else if ?m n. ODD(m) /\ ODD(n) /\ (abs y = &m / &n)
                    then --(exp(y * log(--x)))
                    else exp(y * log(--x))`;;

let RPOW_POW = `!x n. x rpow &n = x pow n`;;

let RPOW_0 = `!x. x rpow &0 = &1`;;

let RPOW_NEG = `!x y. x rpow (--y) = inv(x rpow y)`;;

let RPOW_ZERO = `!y. &0 rpow y = if y = &0 then &1 else &0`;;

let RPOW_POS_LT = `!x y. &0 < x ==> &0 < x rpow y`;;

let RPOW_POS_LE = `!x y. &0 <= x ==> &0 <= x rpow y`;;

let RPOW_LT2 = `!x y z. &0 <= x /\ x < y /\ &0 < z ==> x rpow z < y rpow z`;;

let RPOW_LE2 = `!x y z. &0 <= x /\ x <= y /\ &0 <= z ==> x rpow z <= y rpow z`;;

let REAL_ABS_RPOW = `!x y. abs(x rpow y) = abs(x) rpow y`;;

let RPOW_ONE = `!z. &1 rpow z = &1`;;

let RPOW_RPOW = `!x y z. &0 <= x ==> x rpow y rpow z = x rpow (y * z)`;;

let RPOW_LNEG = `!x y. --x rpow y =
         if ?m n. ODD m /\ ODD n /\ abs y = &m / &n
         then --(x rpow y) else x rpow y`;;

let RPOW_EQ_0 = `!x y. x rpow y = &0 <=> x = &0 /\ ~(y = &0)`;;

let RPOW_MUL = `!x y z. (x * y) rpow z = x rpow z * y rpow z`;;

let RPOW_INV = `!x y. inv(x) rpow y = inv(x rpow y)`;;

let REAL_INV_RPOW = `!x y. inv(x rpow y) = inv(x) rpow y`;;

let RPOW_DIV = `!x y z. (x / y) rpow z = x rpow z / y rpow z`;;

let RPOW_PRODUCT = `!s:A->bool x y.
      FINITE s ==> (product s x) rpow y = product s (\i. x i rpow y)`;;

let RPOW_ADD = `!x y z. &0 < x ==> x rpow (y + z) = x rpow y * x rpow z`;;

let RPOW_SUB = `!x y z. &0 < x ==> x rpow (y - z) = x rpow y / x rpow z`;;

let RPOW_ADD_ALT = `!x y z. &0 <= x /\ (x = &0 /\ y + z = &0 ==> y = &0 \/ z = &0)
           ==> x rpow (y + z) = x rpow y * x rpow z`;;

let RPOW_SUB_ALT = `!x y z. &0 <= x /\ (x = &0 /\ y = z ==> y = &0 \/ z = &0)
           ==> x rpow (y - z) = x rpow y / x rpow z`;;

let RPOW_SQRT = `!x. &0 <= x ==> x rpow (&1 / &2) = sqrt x`;;

let RPOW_MONO_LE = `!a b x. &1 <= x /\ a <= b ==> x rpow a <= x rpow b`;;

let RPOW_MONO_LT = `!a b x. &1 < x /\ a < b ==> x rpow a < x rpow b`;;

let RPOW_MONO_LE_EQ = `!a b x. &1 < x ==> (x rpow a <= x rpow b <=> a <= b)`;;

let RPOW_MONO_LT_EQ = `!a b x. &1 < x ==> (x rpow a < x rpow b <=> a < b)`;;

let RPOW_INJ = `!x y z. &0 < x ==> (x rpow y = x rpow z <=> x = &1 \/ y = z)`;;

let RPOW_LE_1 = `!x y. &1 <= x /\ &0 <= y ==> &1 <= x rpow y`;;

let RPOW_LT_1 = `!x y. &1 < x /\ &0 < y ==> &1 < x rpow y`;;

let RPOW_MONO_INV = `!a b x. &0 < x /\ x <= &1 /\ b <= a ==> x rpow a <= x rpow b`;;

let RPOW_1_LE = `!a x. &0 <= x /\ x <= &1 /\ &0 <= a ==> x rpow a <= &1`;;

let REAL_ROOT_RPOW = `!n x. ~(n = 0) /\ (&0 <= x \/ ODD n) ==> root n x = x rpow (inv(&n))`;;

let LOG_RPOW = `!x y. &0 < x ==> log(x rpow y) = y * log x`;;

let LOG_SQRT = `!x. &0 < x ==> log(sqrt x) = log x / &2`;;

let RPOW_ADD_INTEGER = `!x m n. integer m /\ integer n /\ ~(x = &0 /\ m + n = &0 /\ ~(n = &0))
            ==> x rpow (m + n) = x rpow m * x rpow n`;;

let NORM_CPOW = `!w z. real w /\ &0 < Re w ==> norm(w cpow z) = norm(w) rpow (Re z)`;;

let REAL_MAX_RPOW = `!x y z. &0 <= x /\ &0 <= y /\ &0 <= z
           ==> max (x rpow z) (y rpow z) = (max x y) rpow z`;;

let REAL_MIN_RPOW = `!x y z. &0 <= x /\ &0 <= y /\ &0 <= z
           ==> min (x rpow z) (y rpow z) = (min x y) rpow z`;;

(* ------------------------------------------------------------------------- *)
(* Summability of zeta function series.                                      *)
(* ------------------------------------------------------------------------- *)

let SUMMABLE_ZETA = `!n z. &1 < Re z ==> summable (from n) (\k. inv(Cx(&k) cpow z))`;;

let SUMMABLE_ZETA_INTEGER = `!n m. 2 <= m ==> summable (from n) (\k. inv(Cx(&k) pow m))`;;

(* ------------------------------------------------------------------------- *)
(* Formulation of loop homotopy in terms of maps out of S^1                  *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS = `!f:complex->real^N g s.
        homotopic_with (\h. T)
          (subtopology euclidean (sphere(vec 0,&1)),subtopology euclidean s)
          f g
        ==> homotopic_loops s (f o cexp o (\t. Cx(&2 * pi * drop t) * ii))
                              (g o cexp o (\t. Cx(&2 * pi * drop t) * ii))`;;

let HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS = `!p q s:real^N->bool.
        homotopic_loops s p q
        ==> homotopic_with (\h. T)
             (subtopology euclidean (sphere(vec 0,&1)),subtopology euclidean s)
                                   (p o (\z. lift(Arg z / (&2 * pi))))
                                   (q o (\z. lift(Arg z / (&2 * pi))))`;;

let SIMPLY_CONNECTED_EQ_HOMOTOPIC_CIRCLEMAPS,
    SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP =
 (CONJ_PAIR o prove)
 (`(!s:real^N->bool.
        simply_connected s <=>
        !f g:complex->real^N.
              f continuous_on sphere(vec 0,&1) /\
              IMAGE f (sphere(vec 0,&1)) SUBSET s /\
              g continuous_on sphere(vec 0,&1) /\
              IMAGE g (sphere(vec 0,&1)) SUBSET s
              ==> homotopic_with (\h. T)
                   (subtopology euclidean (sphere(vec 0,&1)),
                    subtopology euclidean s) f g) /\
   (!s:real^N->bool.
      simply_connected s <=>
      path_connected s /\
      !f:real^2->real^N.
              f continuous_on sphere(vec 0,&1) /\
              IMAGE f (sphere(vec 0,&1)) SUBSET s
              ==> ?a. homotopic_with (\h. T)
                       (subtopology euclidean (sphere(vec 0,&1)),
                        subtopology euclidean s) f (\x. a))`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> p) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simply_connected] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`f:complex->real^N`; `g:complex->real^N`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`(f:complex->real^N) o cexp o (\t. Cx(&2 * pi * drop t) * ii)`;
      `(g:complex->real^N) o cexp o (\t. Cx(&2 * pi * drop t) * ii)`]) THEN
    ONCE_REWRITE_TAC[TAUT `p1 /\ q1 /\ r1 /\ p2 /\ q2 /\ r2 <=>
                           (p1 /\ r1 /\ q1) /\ (p2 /\ r2 /\ q2)`] THEN
    REWRITE_TAC[GSYM HOMOTOPIC_LOOPS_REFL] THEN
    ASM_SIMP_TAC[HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS;
                 HOMOTOPIC_WITH_REFL; CONTINUOUS_MAP_EUCLIDEAN2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS) THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    REWRITE_TAC[IN_SPHERE_0; LIFT_DROP; o_DEF] THEN X_GEN_TAC `z:complex` THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MP_TAC(SPEC `z:complex` ARG) THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN SIMP_TAC[PI_POS;
      REAL_FIELD `&0 < pi ==> &2 * pi * x / (&2 * pi) = x`] THEN
    ASM_MESON_TAC[COMPLEX_MUL_SYM];
    DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[PATH_CONNECTED_EQ_HOMOTOPIC_POINTS] THEN
      MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`(\x. a):complex->real^N`; `(\x. b):complex->real^N`]) THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_THEN
       (MP_TAC o MATCH_MP HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS) THEN
      REWRITE_TAC[o_DEF; LINEPATH_REFL];
      X_GEN_TAC `f:complex->real^N` THEN STRIP_TAC THEN
      EXISTS_TAC `f(Cx(&1)):real^N` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0]) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC];
    STRIP_TAC THEN
    ASM_REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME] THEN
    X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `(p:real^1->real^N) o (\z. lift(Arg z / (&2 * pi)))`) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `p:real^1->real^N`]
        HOMOTOPIC_LOOPS_REFL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP
        HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS) THEN
      SIMP_TAC[HOMOTOPIC_WITH_REFL; CONTINUOUS_MAP_EUCLIDEAN2];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
      STRIP_TAC THEN FIRST_ASSUM
       (MP_TAC o MATCH_MP HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; o_DEF] THEN
      DISCH_THEN(MP_TAC o SPEC `Cx(&1)` o CONJUNCT2) THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[LINEPATH_REFL] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMOTOPIC_LOOPS_TRANS) THEN
      MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_INTERVAL_1; FORALL_LIFT; LIFT_DROP; DROP_VEC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t = &1` THENL
       [ASM_REWRITE_TAC[REAL_ARITH `&2 * pi * &1 = &2 * &1 * pi`] THEN
        SIMP_TAC[CEXP_INTEGER_2PI; INTEGER_CLOSED; ARG_NUM] THEN
        REWRITE_TAC[real_div; REAL_MUL_LZERO; LIFT_NUM] THEN
        ASM_MESON_TAC[pathstart; pathfinish];
        AP_TERM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[PI_POS; REAL_FIELD
         `&0 < pi ==> (t = x / (&2 * pi) <=> x = &2 * pi * t)`] THEN
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `Im(Cx (&2 * pi * t) * ii)` THEN
        CONJ_TAC THENL [MATCH_MP_TAC ARG_CEXP; ALL_TAC] THEN
        SIMP_TAC[IM_MUL_II; RE_CX; REAL_ARITH
          `a < &2 * pi <=> a < &2 * pi * &1`] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_LMUL_EQ; REAL_OF_NUM_LT; ARITH;
                     PI_POS; REAL_LT_IMP_LE; REAL_POS; REAL_LE_MUL] THEN
        ASM_REWRITE_TAC[REAL_LT_LE]]]]);;

let HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS = `!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t
        ==> (simply_connected s <=> simply_connected t)`;;

(* ------------------------------------------------------------------------- *)
(* Integration via polar coordinates.                                        *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_POLAR = `!z. ((\w. Cx(Re w) * cexp(ii * Cx(Im w))) has_derivative
        (\h. vector[vector[cos(Im z); --Re(z) * sin(Im z)];
                    vector[sin(Im z); Re z * cos(Im z)]] ** h))
       (at z)`;;

let HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_POLAR = `!f:complex->real^N b.
        f absolutely_integrable_on (:complex) /\ integral (:complex) f = b <=>
        (\z. Re z % f(Cx(Re z) * cexp(ii * Cx(Im z))))
        absolutely_integrable_on
        {z | &0 <= Re z /\ &0 <= Im z /\ Im z <= &2 * pi} /\
        integral {z | &0 <= Re z /\ &0 <= Im z /\ Im z <= &2 * pi}
        (\z. Re z % f(Cx(Re z) * cexp(ii * Cx(Im z)))) = b`;;

let ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES_POLAR = `!f:complex->real^N.
        f absolutely_integrable_on (:complex) <=>
        (\z. Re z % f(Cx(Re z) * cexp(ii * Cx(Im z))))
        absolutely_integrable_on
        {z | &0 <= Re z /\ &0 <= Im z /\ Im z <= &2 * pi}`;;

let FUBINI_POLAR = `!f:complex->real^N.
        f absolutely_integrable_on (:complex)
        ==> negligible
             {r | &0 <= drop r /\
                  ~((\t. drop r % f(Cx(drop r) * cexp(ii * Cx(drop t))))
                    absolutely_integrable_on interval[vec 0,lift(&2 * pi)])} /\
            (\r. integral (interval[vec 0,lift(&2 * pi)])
                   (\t. drop r % f(Cx(drop r) * cexp(ii * Cx(drop t)))))
            absolutely_integrable_on {r | &0 <= drop r} /\
            integral {r | &0 <= drop r}
             (\r. integral (interval[vec 0,lift(&2 * pi)])
                    (\t. drop r % f(Cx(drop r) * cexp(ii * Cx(drop t))))) =
            integral (:complex) f`;;

let FUBINI_TONELLI_POLAR = `!f:complex->real^N.
       f measurable_on (:complex)
       ==> (f absolutely_integrable_on (:complex) <=>
            negligible
             {r | &0 <= drop r /\
                  ~((\t. drop r % f(Cx(drop r) * cexp(ii * Cx(drop t))))
                    absolutely_integrable_on interval[vec 0,lift(&2 * pi)])} /\
            (\r. integral (interval[vec 0,lift(&2 * pi)])
                  (\t. drop r %
                       lift(norm(f(Cx(drop r) * cexp(ii * Cx(drop t)))))))
            integrable_on {r | &0 <= drop r})`;;
