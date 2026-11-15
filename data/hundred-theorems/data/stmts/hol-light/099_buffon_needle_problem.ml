(* ========================================================================= *)
(* Buffon's needle problem -- short and long needle cases.                   *)
(*                                                                           *)
(* A needle of length l is dropped uniformly at random on a floor ruled      *)
(* with parallel lines at distance d apart. The needle's position is         *)
(* described by two independent uniform random variables:                    *)
(*   X ~ Uniform(0, d/2)   (distance from center to nearest line)            *)
(*   Theta ~ Uniform(0, pi) (angle of the needle)                            *)
(* The needle crosses a line iff X <= (l/2) * sin(Theta).                    *)
(*                                                                           *)
(* We first prove a unified general theorem for any l, d > 0, expressing     *)
(* the crossing probability as an integral involving min(d/2, (l/2)*sin).    *)
(* The short and long needle formulas are then derived as special cases:     *)
(*                                                                           *)
(*   Short needle (l <= d):                                                  *)
(*     P(crossing) = 2l / (pi * d)                                           *)
(*                                                                           *)
(*   Long needle (d <= l):                                                   *)
(*     P(crossing) = (2 / (pi * d)) * (l - sqrt(l^2 - d^2) + d * acs(d/l))   *)
(*                                                                           *)
(* Main results:                                                             *)
(*   BUFFON_GENERAL     -- unified integral form for any l, d > 0            *)
(*   BUFFON_SHORT       -- P = 2l/(pi*d) when l <= d                         *)
(*   BUFFON_LONG        -- long needle formula when d <= l                   *)
(* ========================================================================= *)

needs "Probability/measure.ml";;
needs "Probability/random_variables.ml";;
needs "Probability/independence.ml";;
needs "Probability/expectation.ml";;

prioritize_real();;

(* ===================================================================== *)
(* Uniform distribution on an interval                                   *)
(* ===================================================================== *)

let uniform_rv = new_definition
  `uniform_rv (p:A prob_space) (X:A->real) (a:real) (b:real) <=>
   random_variable p X /\
   a < b /\
   !t. distribution_fn p X t =
     if t < a then &0
     else if b <= t then &1
     else (t - a) / (b - a)`;;

(* ===================================================================== *)
(* Basic properties of uniform distributions                             *)
(* ===================================================================== *)

let UNIFORM_RV_IMP_RV = `!p:A prob_space X a b. uniform_rv p X a b ==> random_variable p X`;;

let UNIFORM_RV_BOUNDS = `!p:A prob_space X a b. uniform_rv p X a b ==> a < b`;;

(* CDF value in the middle range *)
let UNIFORM_RV_CDF_MID = `!p:A prob_space X a b t.
      uniform_rv p X a b /\ a <= t /\ t < b
      ==> distribution_fn p X t = (t - a) / (b - a)`;;

(* CDF value at or above b *)
let UNIFORM_RV_CDF_HIGH = `!p:A prob_space X a b t.
      uniform_rv p X a b /\ b <= t
      ==> distribution_fn p X t = &1`;;

(* CDF value below a *)
let UNIFORM_RV_CDF_LOW = `!p:A prob_space X a b t.
      uniform_rv p X a b /\ t < a
      ==> distribution_fn p X t = &0`;;

(* CDF at zero for Uniform(0, b) *)
let UNIFORM_RV_CDF_ZERO = `!p:A prob_space X b t.
      uniform_rv p X (&0) b /\ &0 <= t /\ t < b
      ==> distribution_fn p X t = t / b`;;

(* CDF for Uniform(0, b) at any c in [0, b], including the right endpoint *)
let UNIFORM_ZERO_CDF_RANGE = `!p:A prob_space X b c. uniform_rv p X (&0) b /\ &0 <= c /\ c <= b
   ==> distribution_fn p X c = c / b`;;

(* ===================================================================== *)
(* The integral of sin from 0 to pi                                      *)
(* ===================================================================== *)

(* The key integral: integral of sin from 0 to pi equals 2 *)
let HAS_REAL_INTEGRAL_SIN_0_PI = `(sin has_real_integral (&2)) (real_interval [&0, pi])`;;

(* Scaled version: integral of c * sin from 0 to pi equals 2 * c *)
let HAS_REAL_INTEGRAL_CMUL_SIN_0_PI = `!c. ((\t. c * sin t) has_real_integral (&2 * c))
        (real_interval [&0, pi])`;;

(* ===================================================================== *)
(* Helper lemmas for the bridge proof                                    *)
(* ===================================================================== *)

(* Lipschitz bound for sin: |sin(b) - sin(a)| <= |b - a| *)
let SIN_LIPSCHITZ = `!a b. abs(sin b - sin a) <= abs(b - a)`;;

(* Epsilon-to-equality *)
let REAL_EQ_EPSILON = `!x y:real. (!e. &0 < e ==> abs(x - y) < e) ==> x = y`;;

(* Sandwich bound: both in [L,U] implies |a-b| <= U-L *)
let SANDWICH_ABS_BOUND = `!a b l r. l <= a /\ a <= r /\ l <= b /\ b <= r
              ==> abs(a - b) <= r - l`;;

(* ===================================================================== *)
(* Independence and probability machinery                                *)
(* ===================================================================== *)

(* The joint CDF formula for independent RVs (from indep_rv definition) *)
let INDEP_JOINT_CDF = `!p:A prob_space X Y a b.
      indep_rv p X Y
      ==> prob p {x | x IN prob_carrier p /\ X x <= a /\ Y x <= b} =
          distribution_fn p X a * distribution_fn p Y b`;;

(* Probability of a set difference when one is a subset *)
let PROB_SUBSET_DIFF = `!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ b SUBSET a
      ==> prob p (a DIFF b) = prob p a - prob p b`;;

(* Rectangle probability for independent RVs *)
let INDEP_RECT_PROB = `!p:A prob_space X Theta c a' b'.
      indep_rv p X Theta /\ a' <= b'
      ==> prob p {x | x IN prob_carrier p /\ X x <= c /\
                      a' < Theta x /\ Theta x <= b'} =
          distribution_fn p X c *
          (distribution_fn p Theta b' - distribution_fn p Theta a')`;;

(* Rectangle probability for specific uniform distributions *)
let UNIFORM_RECT_PROB = `!p:A prob_space X Theta d c a' b'.
       uniform_rv p X (&0) (d / &2) /\
       uniform_rv p Theta (&0) pi /\
       indep_rv p X Theta /\
       &0 <= c /\ c <= d / &2 /\
       &0 <= a' /\ a' <= b' /\ b' <= pi
       ==> prob p {x | x IN prob_carrier p /\ X x <= c /\
                       a' < Theta x /\ Theta x <= b'} =
           c / (d / &2) * ((b' - a') / pi)`;;

(* Finite additivity for pairwise disjoint indexed events *)
let PROB_FINITE_ADDITIVE = `!p:A prob_space A.
      !n. (!k. k <= n ==> A k IN prob_events p) /\
          (!i j. i <= n /\ j <= n /\ ~(i = j) ==> DISJOINT (A i) (A j))
          ==> prob p (UNIONS (IMAGE A (0..n))) =
              sum (0..n) (\k. prob p (A k))`;;

(* Paired Skolemization *)
let SKOLEM_PAIR = `(!x:A. ?a:B b:C. P x a b) <=> (?f g. !x. P x (f x) (g x))`;;

(* ===================================================================== *)
(* Generalized Buffon's needle (short and long needle cases)             *)
(*                                                                       *)
(* For arbitrary l, d > 0, the crossing probability equals               *)
(*   (2 / (pi * d)) * integral_0^pi min(d/2, l/2 * sin(t)) dt            *)
(*                                                                       *)
(* When l <= d this gives 2l/(pi*d) (short needle).                      *)
(* When d <= l this gives (2/(pi*d))*(l - sqrt(l^2-d^2) + d*acs(d/l))    *)
(* (long needle, Laplace 1812).                                          *)
(* ===================================================================== *)

(* ----- Helper lemmas for min-clipped sin function ----- *)

(* Lipschitz property of min with a constant: min is a contraction *)
let MIN_CONTRACTION = `!c x y. x <= y ==> min c y - min c x <= y - x`;;

(* Absolute Lipschitz form *)
let MIN_ABS_LIPSCHITZ = `!c x y. abs(min c x - min c y) <= abs(x - y)`;;

(* Oscillation bound for min(d/2, l/2 * sin) on [a,b] within [0,pi] *)
let MIN_SIN_OSCILLATION = `!l d a b. &0 < l /\ &0 < d /\ a <= b /\ &0 <= a /\ b <= pi
    ==> ?m M. (!t. t IN real_interval[a,b]
                 ==> m <= min (d / &2) (l / &2 * sin t) /\
                     min (d / &2) (l / &2 * sin t) <= M) /\
              M - m <= l / &2 * (b - a) /\
              &0 <= m /\ m <= d / &2 /\ M <= d / &2`;;

(* Custom tactic for PROB_SUBADDITIVE that handles alpha-equivalence.
   MATCH_MP_TAC fails when the LHS and RHS sets come from different term
   parsings (same set expressions but different bound variable names).
   This tactic extracts the union from the goal's LHS, instantiates
   PROB_SUBADDITIVE with those exact terms, and uses AP_TERM/ALPHA to
   bridge any alpha-equivalence gap on the RHS. *)
let SUBADDITIVE_TAC : tactic =
  fun (asl, w) ->
    let lhs = lhand w in
    let prob_p = rator lhs in
    let union_set = rand lhs in
    let a_set = lhand union_set in
    let b_set = rand union_set in
    let p_tm = rand prob_p in
    let ith = ISPECL [p_tm; a_set; b_set] PROB_SUBADDITIVE in
    let ant = fst(dest_imp(concl ith)) in
    null_meta, [asl, ant], fun i [pth] ->
      let ith' = INSTANTIATE_ALL i ith in
      let th = MP ith' pth in
      if concl th = w then th
      else
        let rhs_eq = ALPHA (rand(concl th)) (rand w) in
        EQ_MP (AP_TERM (rator(concl th)) rhs_eq) th;;

(* Tactic to rewrite "prob p S = &0" when S is alpha-equivalent to an
   assumption's argument. Handles alpha-equiv bound variable mismatch.
   Goal should be of the form: ... + prob p S <= ...
   where an assumption has |- prob p S' = &0 with S aconv S'. *)
let PROB_ZERO_TAC : tactic =
  fun (asl, w) ->
    let prob_y = rand(lhand w) in
    let target_eq = mk_eq(prob_y, `&0`) in
    let (_, asm_th) = find (fun (_, th) ->
      try let l,r = dest_eq(concl th) in
          aconv l prob_y && r = `&0`
      with _ -> false) asl in
    let bridge =
      if concl asm_th = target_eq then asm_th
      else EQ_MP (ALPHA (concl asm_th) target_eq) asm_th in
    (SUBST1_TAC bridge THEN REWRITE_TAC[REAL_ADD_RID]) (asl, w);;

(* ------------------------------------------------------------------------- *)
(* General core bound: Riemann sum approach with min clipping                *)
(* ------------------------------------------------------------------------- *)

let BUFFON_GENERAL_CORE_BOUND = `!p:A prob_space X Theta l d.
      &0 < l /\ &0 < d /\
      uniform_rv p X (&0) (d / &2) /\
      uniform_rv p Theta (&0) pi /\
      indep_rv p X Theta
      ==> !N. 1 <= N
          ==> abs(prob p {x:A | x IN prob_carrier p /\
                     X x <= l / &2 * sin(Theta x)} -
                  &2 / (d * pi) *
                  real_integral (real_interval [&0,pi])
                    (\t. min (d / &2) (l / &2 * sin t)))
              <= l * pi / (d * &N)`;;

(* ===================================================================== *)
(* BUFFON_GENERAL_BRIDGE: crossing probability = integral formula        *)
(* (epsilon-delta from core bound, no l <= d hypothesis)                 *)
(* ===================================================================== *)

let BUFFON_GENERAL_BRIDGE = `!p:A prob_space X Theta l d.
      &0 < l /\ &0 < d /\
      uniform_rv p X (&0) (d / &2) /\
      uniform_rv p Theta (&0) pi /\
      indep_rv p X Theta
      ==> prob p {x | x IN prob_carrier p /\ X x <= (l / &2) * sin(Theta x)} =
          (&2 / (d * pi)) *
          real_integral (real_interval [&0, pi])
            (\t. min (d / &2) (l / &2 * sin t))`;;

(* ===================================================================== *)
(* BUFFON_GENERAL: unified integral form (commuted coefficient)          *)
(* ===================================================================== *)

let BUFFON_GENERAL = `!p:A prob_space X Theta l d.
      &0 < l /\ &0 < d /\
      uniform_rv p X (&0) (d / &2) /\
      uniform_rv p Theta (&0) pi /\
      indep_rv p X Theta
      ==> prob p {x | x IN prob_carrier p /\ X x <= (l / &2) * sin(Theta x)} =
          (&2 / (pi * d)) *
          real_integral (real_interval [&0, pi])
            (\t. min (d / &2) (l / &2 * sin t))`;;

(* ===================================================================== *)
(* Short needle integral: when l <= d, min(d/2, l/2*sin t) = l/2*sin t  *)
(* ===================================================================== *)

let MIN_SIN_INTEGRAL_SHORT = `!l d. &0 < l /\ &0 < d /\ l <= d
      ==> real_integral (real_interval [&0, pi])
            (\t. min (d / &2) (l / &2 * sin t)) = l`;;

(* ===================================================================== *)
(* BUFFON_SHORT: re-derive the short needle formula from general         *)
(* ===================================================================== *)

let BUFFON_SHORT = `!p:A prob_space X Theta l d.
      &0 < l /\ l <= d /\ &0 < d /\
      uniform_rv p X (&0) (d / &2) /\
      uniform_rv p Theta (&0) pi /\
      indep_rv p X Theta
      ==> prob p {x | x IN prob_carrier p /\ X x <= (l / &2) * sin(Theta x)} =
          (&2 * l) / (pi * d)`;;

(* ===================================================================== *)
(* Long needle integral evaluation: when d <= l,                         *)
(*   integral_0^pi min(d/2, l/2 * sin t) dt                             *)
(*     = l - sqrt(l^2 - d^2) + d * acs(d/l)                             *)
(* ===================================================================== *)

(* Helper: sin(pi - x) = sin(x) *)
let SIN_PI_SUB = `!x. sin(pi - x) = sin(x)`;;

(* Helper: cos(pi - x) = --(cos x) *)
let COS_PI_SUB = `!x. cos(pi - x) = --(cos(x))`;;

(* Helper: integral of sin over [a,b] = cos(a) - cos(b) via FTC *)
let HAS_REAL_INTEGRAL_SIN = `!a b. a <= b
     ==> (sin has_real_integral (cos(a) - cos(b))) (real_interval [a, b])`;;

(* Helper: integral of c*sin over [a,b] = c*(cos(a) - cos(b)) *)
let HAS_REAL_INTEGRAL_CMUL_SIN = `!c a b. a <= b
     ==> ((\t. c * sin t) has_real_integral (c * (cos a - cos b)))
          (real_interval [a, b])`;;

let MIN_SIN_INTEGRAL_LONG = `!l d. &0 < l /\ &0 < d /\ d <= l
      ==> real_integral (real_interval [&0, pi])
            (\t. min (d / &2) (l / &2 * sin t)) =
          l - sqrt(l pow 2 - d pow 2) + d * acs(d / l)`;;

(* ===================================================================== *)
(* BUFFON_LONG: long needle formula from general                         *)
(* ===================================================================== *)

let BUFFON_LONG = `!p:A prob_space X Theta l d.
      &0 < l /\ &0 < d /\ d <= l /\
      uniform_rv p X (&0) (d / &2) /\
      uniform_rv p Theta (&0) pi /\
      indep_rv p X Theta
      ==> prob p {x | x IN prob_carrier p /\ X x <= (l / &2) * sin(Theta x)} =
          (&2 / (pi * d)) *
          (l - sqrt(l pow 2 - d pow 2) + d * acs(d / l))`;;
