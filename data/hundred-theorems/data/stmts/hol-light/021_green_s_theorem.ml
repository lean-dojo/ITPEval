(* ========================================================================= *)
(* Green's theorem for rectifiable Jordan curves via the Cauchy transform.   *)
(*                                                                           *)
(* MAIN RESULT (COMPLEX_GREEN):                                              *)
(*   For f locally C^1 near the curve, g a rectifiable closed path:          *)
(*     (1/2i) path_integral g f                                              *)
(*       = integral_C winding_number(g,z) * dbar(f)(z) dA(z)                 *)
(*                                                                           *)
(* COROLLARIES:                                                              *)
(*   COMPLEX_GREEN_ALT    -- with Cx(Re(winding_number)) (technical form)    *)
(*   COMPLEX_GREEN_INSIDE -- integral restricted to inside(path_image g)     *)
(*   GREEN_THEOREM_CURL   -- real curl form with partial derivatives         *)
(*   GREEN_AREA_ABS       -- orientation-free area via path integral         *)
(*                                                                           *)
(* HIGH-LEVEL PROOF STRATEGY                                                 *)
(*                                                                           *)
(* The approach avoids the usual regularity theory for the Riemann mapping   *)
(* or smoothing/approximation of the boundary curve. Instead, it uses the    *)
(* Cauchy transform (the convolution operator Tf(w) = integral f(z)/(z-w))   *)
(* as a left inverse of the d-bar operator, inspired by Kostya_I's answer:   *)
(*   https://mathoverflow.net/questions/307713                               *)
(* The technique is rooted in the Cauchy transform / dbar framework of       *)
(* Ahlfors, "Lectures on Quasiconformal Mappings" (1966, 2nd ed. 2006),      *)
(* and appears in Bonk's UCLA complex analysis lecture notes, Ch. 20:        *)
(*   https://www.math.ucla.edu/~mbonk/complana.pdf                           *)
(* The key steps are:                                                        *)
(*                                                                           *)
(* 1. POMPEIU FORMULA (CAUCHY_TRANSFORM_INVERTS_DBAR):                       *)
(*    For f in C^1_c(C), integral dbar(f)(z)/(z-w) dA(z) = -pi*f(w).         *)
(*    Proved via polar coordinates and integration by parts.                 *)
(*    See Ahlfors, "Complex Analysis", Ch.5; Bonk, lecture notes, Lemma 20.  *)
(*                                                                           *)
(* 2. FUBINI EXCHANGE (FUBINI_PATH_AREA):                                    *)
(*    Swap the path integral and area integral:                              *)
(*      integral_C (integral_gamma f(z)/(z-w) |dw|) dA(z)                    *)
(*        = integral_gamma (integral_C f(z)/(z-w) dA(z)) |dw|                *)
(*    Uses product-space absolute integrability (Lp estimates + Holder).     *)
(*                                                                           *)
(* 3. SMOOTH EXTENSION (SMOOTH_EXTENSION_FROM_OPEN):                         *)
(*    Given f locally C^1 near the curve, extend to a C^1 function with      *)
(*    compact support on all of C. Uses Hermite cutoff functions composed    *)
(*    with a finite ball cover (Lebesgue number lemma).                      *)
(*                                                                           *)
(* 4. ASSEMBLY (COMPLEX_GREEN_ALT):                                          *)
(*    Combine Pompeiu + Fubini: the path integral of f equals an area        *)
(*    integral of winding_number * dbar(f). The winding number appears       *)
(*    because the Cauchy kernel 1/(z-w) integrated along the path gives      *)
(*    2*pi*i*winding_number(g,w) by definition. The smooth extension step    *)
(*    reduces the local C^1 case to the global C^1 case.                     *)
(* ========================================================================= *)

needs "Multivariate/cauchy.ml";;
needs "Multivariate/lpspaces.ml";;

prioritize_real();;

(* ========================================================================= *)
(* The Wirtinger (d-bar) derivative.                                         *)
(*                                                                           *)
(* For a real-differentiable function f: C -> C with Jacobian J at z:        *)
(*   df/dz-bar = (1/2)(J11 - J22 + i*(J21 + J12))                            *)
(*             = (1/2)(df/dx + i*df/dy)                                      *)
(*                                                                           *)
(* f is holomorphic iff df/dz-bar = 0 (Cauchy-Riemann equations).            *)
(* ========================================================================= *)

(* The d-bar derivative in terms of the Jacobian matrix                      *)
let wirtinger_dbar = new_definition
 `wirtinger_dbar (f:complex->complex) (z:complex) =
    complex((jacobian f (at z))$1$1 - (jacobian f (at z))$2$2,
            (jacobian f (at z))$2$1 + (jacobian f (at z))$1$2) / Cx(&2)`;;

(* The holomorphic Wirtinger derivative df/dz                                *)
let wirtinger_dz = new_definition
 `wirtinger_dz (f:complex->complex) (z:complex) =
    complex((jacobian f (at z))$1$1 + (jacobian f (at z))$2$2,
            (jacobian f (at z))$2$1 - (jacobian f (at z))$1$2) / Cx(&2)`;;

(* ------------------------------------------------------------------------- *)
(* Key property: wirtinger_dbar = 0 iff f is holomorphic.                    *)
(* This is exactly the Cauchy-Riemann equations.                             *)
(* ------------------------------------------------------------------------- *)

let WIRTINGER_DBAR_EQ_ZERO = `!f z. f differentiable (at z)
         ==> (wirtinger_dbar f z = Cx(&0) <=>
              f complex_differentiable (at z))`;;

(* ------------------------------------------------------------------------- *)
(* When f is holomorphic, wirtinger_dz agrees with complex_derivative.       *)
(* ------------------------------------------------------------------------- *)

let WIRTINGER_DZ_COMPLEX_DERIVATIVE = `!f z. f complex_differentiable (at z)
         ==> wirtinger_dz f z = complex_derivative f z`;;

(* ------------------------------------------------------------------------- *)
(* The Jacobian can be recovered from wirtinger_dz and wirtinger_dbar.       *)
(* This is the real content: the Jacobian acts as                            *)
(*   J(h) = dz(f) * h + dbar(f) * cnj(h)                                     *)
(* which connects the real derivative to the Wirtinger operators.            *)
(* ------------------------------------------------------------------------- *)

let FRECHET_WIRTINGER = `!f f' z. (f has_derivative f') (at z)
            ==> !h:complex. f'(h) =
                    wirtinger_dz f z * h + wirtinger_dbar f z * cnj h`;;

(* ------------------------------------------------------------------------- *)
(* Wirtinger d-bar of z-bar is 1 (conjugation).                              *)
(* This is a key test: d/dz-bar(z-bar) = 1.                                  *)
(* We need the Jacobian of the conjugation function.                         *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_CNJ = `!z. (cnj has_derivative cnj) (at z)`;;

(* ------------------------------------------------------------------------- *)
(* Wirtinger d-bar of specific simple functions.                             *)
(* We compute d-bar(z-bar) = 1, which is needed for the area formula.        *)
(* This requires computing the Jacobian of conjugation.                      *)
(* ------------------------------------------------------------------------- *)

(* Jacobian of conjugation: cnj(x + iy) = x - iy, so J = [[1,0],[0,-1]]      *)
let JACOBIAN_CNJ = `!z. jacobian cnj (at z) = (vector[vector[&1;&0]; vector[&0;-- &1]]:real^2^2)`;;

let WIRTINGER_DBAR_CNJ = `wirtinger_dbar cnj = \z. Cx(&1)`;;

let WIRTINGER_DBAR_I = `wirtinger_dbar I = \z. Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* Wirtinger d-bar is continuous when the Jacobian is continuous.            *)
(* This is needed for the Fubini step in the Gauss-Green proof.              *)
(* ------------------------------------------------------------------------- *)

let WIRTINGER_DBAR_FRECHET = `!f:complex->complex z.
        wirtinger_dbar f z =
        (frechet_derivative f (at z) (Cx(&1)) +
         ii * frechet_derivative f (at z) ii) / Cx(&2)`;;

let WIRTINGER_DBAR_CONTINUOUS = `!f:complex->complex s.
        (!h. (\z. frechet_derivative f (at z) h) continuous_on s)
        ==> (\z. wirtinger_dbar f z) continuous_on s`;;

(* Wirtinger d-bar has bounded support when f does                           *)
let WIRTINGER_DBAR_BOUNDED_SUPPORT = `!f:complex->complex.
        f differentiable_on (:complex) /\
        bounded (support (+) f (:complex))
        ==> bounded (support (+) (wirtinger_dbar f) (:complex))`;;

(* ========================================================================= *)
(* The Cauchy transform inverts the d-bar operator (Pompeiu formula).        *)
(*                                                                           *)
(* The Cauchy transform of g is Tg(w) = (1/pi) int g(z)/(z-w) dA(z).         *)
(* For f in C^1_c(C), T(dbar f) = -f, or equivalently:                       *)
(*   integral (dbar f)(z) / (z - w) dA(z) = -pi * f(w)                       *)
(*                                                                           *)
(* This is the key identity CAUCHY_TRANSFORM_INVERTS_DBAR below.             *)
(* See Ahlfors, "Complex Analysis" Ch.4 Sec.6; Bonk, lecture notes,          *)
(* Lemma 20.2; Ahlfors QC Ch.5.                                              *)
(*                                                                           *)
(* Proof approach: polar coordinates centered at w, integration by parts.    *)
(* We state the theorem with explicit hypotheses rather than defining        *)
(* the Cauchy transform or C^1_c as HOL Light constants.                     *)
(* ========================================================================= *)

(* ----- Proof sketch for CAUCHY_TRANSFORM_INVERTS_DBAR -----                *)
(*                                                                           *)
(* Let g(r,t) = f(w + r * exp(i*t)). Then:                                   *)
(*   (dbar f)(w + r*exp(it)) = exp(it)/2 * [dg/dr + (i/r)*dg/dt]             *)
(*                                                                           *)
(* The integrand (dbar f)(z) / (z - w) in polar becomes:                     *)
(*   (dbar f)(w + r*exp(it)) * exp(-it)/r * r  [Jacobian = r]                *)
(*   = (dbar f)(w + r*exp(it)) * exp(-it)                                    *)
(*   = (1/2) * [dg/dr + (i/r)*dg/dt]                                         *)
(*                                                                           *)
(* After Fubini (r from 0 to R, t from 0 to 2*pi):                           *)
(*   integral = (1/2) int_0^{2pi} int_0^R dg/dr dr dt                        *)
(*            + (i/2) int_0^R (1/r) int_0^{2pi} dg/dt dt dr                  *)
(*                                                                           *)
(* Radial part: by FTC, int_0^R dg/dr dr = g(R,t) - g(0,t)                   *)
(*   = 0 - f(w) = -f(w) for large R (compact support).                       *)
(*   Hence = (1/2) * 2*pi * (-f(w)) = -pi * f(w).                            *)
(*                                                                           *)
(* Angular part: int_0^{2pi} dg/dt dt = g(r,2pi) - g(r,0) = 0                *)
(*   (periodicity of exp). So this part = 0.                                 *)
(*                                                                           *)
(* Total: -pi * f(w). QED.                                                   *)

(* Sub-lemma: translation reduces to w = 0                                   *)
let CAUCHY_TRANSFORM_DBAR_TRANSLATION = `!f:complex->complex w.
        integral (:complex) (\z. wirtinger_dbar f z / (z - w)) =
        integral (:complex) (\z. wirtinger_dbar f (w + z) / z)`;;

(* Helper lemmas for the polar coordinates proof                             *)

let CONTINUOUS_ON_TRANSLATE_UNIV = `!f:complex->complex a.
        f continuous_on (:complex)
        ==> (\z. f(a + z)) continuous_on (:complex)`;;

let BOUNDED_SUPPORT_TRANSLATE = `!f:complex->complex a.
        bounded (support (+) f (:complex))
        ==> bounded (support (+) (\z. f(a + z)) (:complex))`;;

let POLAR_SIMPLIFY = `!g:complex (r:real^1) (e:complex).
        &0 < drop r /\ ~(e = Cx(&0))
        ==> drop r % (g / (Cx(drop r) * e)) = g * inv e`;;

let INV_CEXP_II = `!t. inv(cexp(ii * Cx t)) = cnj(cexp(ii * Cx t))`;;

let POLAR_CEXP_SIMPLIFY = `!g:complex (r:real^1) t.
        &0 < drop r
        ==> drop r % (g / (Cx(drop r) * cexp(ii * Cx(drop t)))) =
            g * cnj(cexp(ii * Cx(drop t)))`;;

let WIRTINGER_DBAR_FRECHET_POLAR = `!f:complex->complex z e.
        f differentiable at z
        ==> frechet_derivative f (at z) e +
            ii * frechet_derivative f (at z) (ii * e) =
            Cx(&2) * wirtinger_dbar f z * cnj e`;;

let CEXP_2PII = `cexp(ii * Cx(&2 * pi)) = Cx(&1)`;;

let CEXP_0II = `cexp(ii * Cx(&0)) = Cx(&1)`;;

(* ========================================================================= *)
(* Absolutely integrable cpow.                                               *)
(* Uses polar Fubini to show (z - w) cpow p is integrable on bounded sets    *)
(* for Re p > -2.                                                            *)
(* ========================================================================= *)

let NORM_CPOW_COMPLEX = `!w z. real z
         ==> norm(w cpow z) =
             if w = Cx(&0) /\ z = Cx(&0) then &0 else norm(w) rpow (Re z)`;;

let ABSOLUTELY_INTEGRABLE_CPOW = `!s p w.
        bounded s /\ measurable s /\ real p /\ --(&2) < Re p
        ==> (\z. (z - w) cpow p) absolutely_integrable_on s`;;

(* ------------------------------------------------------------------------- *)
(* inv(z - w) is absolutely integrable on bounded measurable sets.           *)
(* ------------------------------------------------------------------------- *)

let INV_ABSOLUTELY_INTEGRABLE_BOUNDED = `!s w:complex.
        bounded s /\ measurable s
        ==> (\z. inv(z - w)) absolutely_integrable_on s`;;

(* ========================================================================= *)
(* Lp-based infrastructure.                                                  *)
(* Uses Holder's inequality and Lp-space theory to prove integrability of    *)
(* Cauchy-type kernels f(z)/(z-w).                                           *)
(* ========================================================================= *)

let LSPACE_COMPLEX_INV = `!s p w:complex.
      bounded s /\ measurable s /\ p < &2 ==> (\z. inv(z - w)) IN lspace s p`;;

(* ------------------------------------------------------------------------- *)
(* u(z) / (z - w) is absolutely integrable for compactly supported u.        *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE = `!u:complex->complex w.
        u continuous_on (:complex) /\
        bounded (support (+) u (:complex))
        ==> (\z. u(z) / (z - w)) absolutely_integrable_on (:complex)`;;

(* ------------------------------------------------------------------------- *)
(* Helper: if-then-else with constant predicate under integral.              *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_IF_CONST = `!s P (f:real^M->real^N).
    integral s (\y. if P then f y else vec 0) =
    if P then integral s f else vec 0`;;

(* ------------------------------------------------------------------------- *)
(* Negligibility of a graph in the product space real^1 x complex.           *)
(* The graph {(x,y) | y = h(x)} is a 1-dim curve in 3-dim space.             *)
(* Uses FUBINI_TONELLI_NEGLIGIBLE: each x-slice is a singleton (negligible). *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_GRAPH_PRODUCT = `!h:real^1->complex. h measurable_on (:real^1) ==>
    negligible {p:real^(1,2)finite_sum | sndcart p = h(fstcart p)}`;;

(* ------------------------------------------------------------------------- *)
(* Measurability of the Fubini integrand on the product space.               *)
(* Key idea: extend g from [0,1] to all of R via Tietze, then factor the     *)
(* function as u(y) * inv(y - G(x)) * (if x IN [0,1] then g'(x) else 0).     *)
(* Each factor is measurable using standard library lemmas.                  *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_FUBINI_INTEGRAND = `!u:complex->complex g:real^1->complex.
    u continuous_on (:complex) /\
    g absolutely_continuous_on interval[vec 0,vec 1]
    ==> (\p:real^(1,2)finite_sum.
            if fstcart p IN interval[vec 0,vec 1]
            then u(sndcart p) / (sndcart p - g(fstcart p)) *
                 vector_derivative g (at (fstcart p))
            else vec 0)
        measurable_on (:real^(1,2)finite_sum)`;;

(* ------------------------------------------------------------------------- *)
(* Uniform bound on Cauchy kernel L^1 norm over compact sets of poles.       *)
(* For w in compact K, integral |u(y)/(y-w)| dy <= C uniformly.              *)
(* Key tool: cball(0,R) subset cball(w,R+S) + translation of integral.       *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_KERNEL_NORM_UNIFORM_BOUND = `!u:complex->complex K.
        u continuous_on (:complex) /\
        bounded (support (+) u (:complex)) /\
        compact K
        ==> ?C. &0 <= C /\
                !w. w IN K ==>
                  drop(integral (:complex)
                       (\y. lift(norm(u y / (y - w))))) <= C`;;

(* ------------------------------------------------------------------------- *)
(* Measurability of the weighted Cauchy kernel norm integral on [0,1].       *)
(* Uses dominated convergence to show continuity and convergence of          *)
(* truncated integrals, then MEASURABLE_ON_LIMIT + MEASURABLE_ON_DROP_MUL.   *)
(* ------------------------------------------------------------------------- *)

let SUPPORT_BOUNDED_OUTSIDE = `!(u:real^M->real^N) R y.
    (!z. z IN support (+) u (:real^M) ==> norm z <= R) /\
    norm(y) > R ==> u y = vec 0`;;

let CAUCHY_KERNEL_NORM_TRUNC_INTEGRABLE = `!u:complex->complex w:complex n:num.
    u continuous_on (:complex) /\ bounded(support (+) u (:complex))
    ==> (\y. lift(real_min (norm(u y / (y - w))) (&n)))
        integrable_on (:complex)`;;

let CAUCHY_KERNEL_NORM_TRUNC_CONTINUOUS = `!u:complex->complex n:num.
    u continuous_on (:complex) /\ bounded(support (+) u (:complex))
    ==> (\w. integral (:complex)
               (\y. lift(real_min (norm(u y / (y - w))) (&n))))
        continuous_on (:complex)`;;

let CAUCHY_KERNEL_NORM_TRUNC_CONVERGES = `!u:complex->complex w:complex.
    u continuous_on (:complex) /\ bounded(support (+) u (:complex))
    ==> ((\n. integral (:complex)
               (\y. lift(real_min (norm(u y / (y - w))) (&n))))
         --> integral (:complex)
               (\y. lift(norm(u y / (y - w))))) sequentially`;;

let CAUCHY_KERNEL_WEIGHTED_MEASURABLE = `!u:complex->complex g:real^1->complex.
    u continuous_on (:complex) /\ bounded(support (+) u (:complex)) /\
    g absolutely_continuous_on interval[vec 0,vec 1]
    ==> (\x. norm(vector_derivative g (at x)) %
             integral (:complex) (\y. lift(norm(u y / (y - g x)))))
        measurable_on interval[vec 0, vec 1]`;;

(* ------------------------------------------------------------------------- *)
(* Fubini exchange: swap path integral and area integral.                    *)
(* Uses FUBINI_INTEGRAL_SWAP on the product space real^1 x complex.          *)
(* LMUL integrability handled via INTEGRAL_SPIKE + NEGLIGIBLE_AC_PATH.       *)
(* ------------------------------------------------------------------------- *)

(* AC path image is negligible (measure zero in R^2)                         *)
let NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE = `!g:real^1->complex.
    g absolutely_continuous_on interval[vec 0,vec 1]
    ==> negligible(path_image g)`;;

let PATH_INTEGRABLE_CONTINUOUS_ABSOLUTELY_CONTINUOUS = `!f:complex->complex g:real^1->complex.
    f continuous_on path_image g /\
    g absolutely_continuous_on interval[vec 0,vec 1]
    ==> f path_integrable_on g`;;

let FUBINI_PATH_AREA = `!u:complex->complex g.
        u continuous_on (:complex) /\
        bounded (support (+) u (:complex)) /\
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g
        ==> path_integral g (\w. integral (:complex)
               (\z. u(z) / (z - w))) =
            integral (:complex)
               (\z. u(z) * path_integral g (\w. Cx(&1) / (z - w)))`;;

(* ------------------------------------------------------------------------- *)
(* Absolute integrability of the translated dbar kernel.                     *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_DBAR_KERNEL = `!f:complex->complex w.
        (\z. wirtinger_dbar f z) continuous_on (:complex) /\
        bounded (support (+) (wirtinger_dbar f) (:complex))
        ==> (\z. wirtinger_dbar f (w + z) / z) absolutely_integrable_on
            (:complex)`;;

(* ------------------------------------------------------------------------- *)
(* Angular / polar path lemmas for polar coordinates proof.                  *)
(* ------------------------------------------------------------------------- *)

(* Derivative chain: t -> Cx(drop t)                                         *)
let HAS_DERIVATIVE_CX_DROP = `!t:real^1. ((\t. Cx(drop t)) has_derivative (\h. Cx(drop h))) (at t)`;;

(* Derivative chain: t -> ii * Cx(drop t)                                    *)
let HAS_DERIVATIVE_II_CX_DROP = `!t:real^1. ((\t. ii * Cx(drop t)) has_derivative (\h. ii * Cx(drop h)))
              (at t)`;;

(* Derivative chain: t -> cexp(ii * Cx(drop t))                              *)
let HAS_DERIVATIVE_CEXP_POLAR = `!t:real^1. ((\t. cexp(ii * Cx(drop t))) has_derivative
      (\h. cexp(ii * Cx(drop t)) * (ii * Cx(drop h)))) (at t)`;;

(* Affine map z -> w + c*z has derivative h -> c*h                           *)
let HAS_DERIVATIVE_AFFINE_MUL = `!c:complex w:complex a:complex.
     ((\z. w + c * z) has_derivative (\h. c * h)) (at a)`;;

(* Derivative of full polar path t -> w + Cx(r) * cexp(ii * Cx(drop t))      *)
let HAS_DERIVATIVE_POLAR_PATH = `!w:complex r t:real^1.
     ((\t. w + Cx r * cexp(ii * Cx(drop t))) has_derivative
      (\h. Cx r * (cexp(ii * Cx(drop t)) * (ii * Cx(drop h))))) (at t)`;;


(* Continuity helper: (\z. c * z) continuous on (:complex)                   *)
let CONTINUOUS_ON_COMPLEX_LMUL_FN = `!c:complex. (\z:complex. c * z) continuous_on (:complex)`;;

(* Continuity: t -> ii * Cx(drop t) on (:real^1)                             *)
let CONT_II_CX_DROP = `(\t:real^1. ii * Cx(drop t)) continuous_on (:real^1)`;;

(* Continuity: t -> cexp(ii * Cx(drop t)) on (:real^1)                       *)
let CONT_CEXP_POLAR = `(\t:real^1. cexp(ii * Cx(drop t))) continuous_on (:real^1)`;;

(* Continuity: full polar path on (:real^1)                                  *)
let CONTINUOUS_ON_POLAR_PATH = `!w:complex r.
     (\t. w + Cx r * cexp(ii * Cx(drop t))) continuous_on (:real^1)`;;

(* Continuity on the interval [0, 2*pi]                                      *)
let CONTINUOUS_ON_POLAR_PATH_INTERVAL = `!w:complex r.
     (\t. w + Cx r * cexp(ii * Cx(drop t))) continuous_on
     interval[vec 0:real^1, lift(&2 * pi)]`;;

(* f composed with polar path continuous                                     *)
let CONTINUOUS_ON_F_POLAR = `!f:complex->complex w r.
     f continuous_on (:complex)
     ==> (\t. f(w + Cx r * cexp(ii * Cx(drop t)))) continuous_on
         interval[vec 0:real^1, lift(&2 * pi)]`;;

(* Vector derivative of f composed with polar path                           *)
let HAS_VECTOR_DERIVATIVE_F_POLAR = `!f:complex->complex w r t.
     f differentiable at (w + Cx r * cexp(ii * Cx(drop t)))
     ==> ((\t. f(w + Cx r * cexp(ii * Cx(drop t))))
          has_vector_derivative
          (frechet_derivative f (at (w + Cx r * cexp(ii * Cx(drop t))))
            (Cx r * cexp(ii * Cx(drop t)) * ii)))
         (at t)`;;

(* Angular FTC: integral of derivative along polar path                      *)
let ANGULAR_FTC = `!f:complex->complex w r.
     f continuous_on (:complex) /\
     f differentiable_on (:complex)
     ==> ((\t. frechet_derivative f (at (w + Cx r * cexp(ii * Cx(drop t))))
                (Cx r * cexp(ii * Cx(drop t)) * ii))
          has_integral
          (f(w + Cx r * cexp(ii * Cx(drop(lift(&2 * pi))))) -
           f(w + Cx r * cexp(ii * Cx(drop(vec 0))))))
         (interval[vec 0, lift(&2 * pi)])`;;

(* The angular integral is zero by 2*pi-periodicity of exp                   *)
let ANGULAR_INTEGRAL_ZERO = `!f:complex->complex w r.
     f continuous_on (:complex) /\
     f differentiable_on (:complex)
     ==> integral (interval[vec 0, lift(&2 * pi)])
           (\t. frechet_derivative f (at (w + Cx r * cexp(ii * Cx(drop t))))
                  (Cx r * cexp(ii * Cx(drop t)) * ii)) = vec 0`;;

(* ========================================================================= *)
(* Frechet derivative commutes with real scalar multiplication               *)
(* ========================================================================= *)

let FRECHET_DERIVATIVE_CX_LMUL = `!f:complex->complex z c x.
     f differentiable at z
     ==> frechet_derivative f (at z) (Cx c * x) =
         Cx c * frechet_derivative f (at z) x`;;

(* For r != 0, the angular integral of f'(z)(ii * exp(it)) is zero           *)
let ANGULAR_INTEGRAL_II_ZERO = `!f:complex->complex w r.
     f continuous_on (:complex) /\
     f differentiable_on (:complex) /\
     ~(r = &0)
     ==> integral (interval[vec 0, lift(&2 * pi)])
           (\t. frechet_derivative f
                  (at (w + Cx r * cexp(ii * Cx(drop t))))
                  (ii * cexp(ii * Cx(drop t)))) = vec 0`;;

(* ========================================================================= *)
(* Radial path lemmas for polar coordinates proof                            *)
(* ========================================================================= *)

(* Radial path: r -> w + Cx(drop r) * cexp(ii * Cx t0)  for fixed t0         *)

let HAS_DERIVATIVE_RADIAL_PATH = `!w:complex t0:real r:real^1.
     ((\r. w + Cx(drop r) * cexp(ii * Cx t0)) has_derivative
      (\h. Cx(drop h) * cexp(ii * Cx t0))) (at r)`;;


let HAS_VECTOR_DERIVATIVE_F_RADIAL = `!f:complex->complex w t0 r.
     f differentiable at (w + Cx(drop r) * cexp(ii * Cx t0))
     ==> ((\r. f(w + Cx(drop r) * cexp(ii * Cx t0)))
          has_vector_derivative
          (frechet_derivative f (at (w + Cx(drop r) * cexp(ii * Cx t0)))
            (cexp(ii * Cx t0))))
         (at r)`;;

(* The radial path is continuous                                             *)
let CONTINUOUS_ON_RADIAL_PATH = `!w:complex t0. (\r:real^1. w + Cx(drop r) * cexp(ii * Cx t0))
                  continuous_on (:real^1)`;;

(* Continuity of f composed with radial path                                 *)
let CONTINUOUS_ON_F_RADIAL = `!f:complex->complex w t0.
     f continuous_on (:complex)
     ==> (\r. f(w + Cx(drop r) * cexp(ii * Cx t0))) continuous_on
         {r:real^1 | &0 <= drop r}`;;

(* Radial FTC for f on [0, R]                                                *)
let RADIAL_FTC = `!f:complex->complex w t0 R.
     f continuous_on (:complex) /\
     f differentiable_on (:complex) /\
     &0 < R
     ==> ((\r. frechet_derivative f
                (at (w + Cx(drop r) * cexp(ii * Cx t0)))
                (cexp(ii * Cx t0)))
          has_integral
          (f(w + Cx R * cexp(ii * Cx t0)) - f(w)))
         (interval[vec 0, lift R])`;;


(* For r > 0, the inner polar integral simplifies:                           *)
(* drop r % (dbar f z / (Cx(drop r) * cexp)) =                               *)
(*   inv(Cx 2) * integral [0,2pi] f'(z)(cexp)                                *)
(* Uses: POLAR_CEXP_SIMPLIFY + WIRTINGER_DBAR_FRECHET_POLAR +                *)
(*       ANGULAR_INTEGRAL_II_ZERO                                            *)

let INNER_INTEGRAL_SIMPLIFY = `!f:complex->complex w r.
     f continuous_on (:complex) /\
     f differentiable_on (:complex) /\
     (!h. (\z. frechet_derivative f (at z) h) continuous_on (:complex)) /\
     &0 < drop r
     ==> integral (interval[vec 0, lift(&2 * pi)])
           (\t. drop r %
                (wirtinger_dbar f (w + Cx(drop r) * cexp(ii * Cx(drop t))) /
                 (Cx(drop r) * cexp(ii * Cx(drop t))))) =
         inv(Cx(&2)) *
         integral (interval[vec 0, lift(&2 * pi)])
           (\t. frechet_derivative f
                  (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                  (cexp(ii * Cx(drop t))))`;;

(* For each fixed angle t, the radial integral from 0 to infinity            *)
(* of the radial derivative equals -f(w) (by FTC + compact support).         *)

let RADIAL_INTEGRAL_NEG_FW = `!f:complex->complex w t0.
     f continuous_on (:complex) /\
     f differentiable_on (:complex) /\
     bounded (support (+) f (:complex))
     ==> integral {r:real^1 | &0 <= drop r}
           (\r. frechet_derivative f
                  (at (w + Cx(drop r) * cexp(ii * Cx t0)))
                  (cexp(ii * Cx t0))) = --(f w)`;;

(* Helper: in real^1, nonneg and nonzero means positive                      *)
let DROP_POS_OF_NONNEG_NZ = `!r:real^1. &0 <= drop r /\ ~(r = vec 0) ==> &0 < drop r`;;

(* ------------------------------------------------------------------------- *)
(* Helpers for Fubini swap of polar integrals.                               *)
(* ------------------------------------------------------------------------- *)

let WIRTINGER_DZ_FRECHET = `!f:complex->complex z.
        wirtinger_dz f z =
        (frechet_derivative f (at z) (Cx(&1)) -
         ii * frechet_derivative f (at z) ii) / Cx(&2)`;;

let WIRTINGER_DZ_CONTINUOUS = `!f:complex->complex s.
        (!h. (\z. frechet_derivative f (at z) h) continuous_on s)
        ==> (\z. wirtinger_dz f z) continuous_on s`;;

let FRECHET_CONTINUOUS_ON_JOINT = `!f:complex->complex (g:real^P->complex) (h:real^P->complex) s.
        f differentiable_on (:complex) /\
        (!e. (\z. frechet_derivative f (at z) e) continuous_on (:complex)) /\
        g continuous_on s /\
        h continuous_on s
        ==> (\x. frechet_derivative f (at (g x)) (h x)) continuous_on s`;;

let CONTINUOUS_ON_CEXP_SNDCART = `!s. (\z:real^(1,1)finite_sum.
          cexp(ii * Cx(drop(sndcart z)))) continuous_on s`;;

let CONTINUOUS_ON_POLAR_PASTECART = `!w:complex s.
     (\z:real^(1,1)finite_sum.
        w + Cx(drop(fstcart z)) * cexp(ii * Cx(drop(sndcart z))))
     continuous_on s`;;

let FRECHET_DERIVATIVE_ZERO_OUTSIDE = `!f:real^M->real^N z h R.
    f differentiable_on (:real^M) /\
    (!y. R < norm y ==> f y = vec 0) /\
    R < norm z
    ==> frechet_derivative f (at z) h = vec 0`;;

let ZERO_OUTSIDE_SUPPORT_BALL = `!f:real^M->real^N R.
    (!x. x IN support (+) f (:real^M) ==> norm x <= R)
    ==> (!y. R < norm y ==> f y = vec 0)`;;

let POLAR_POINT_NORM_BOUND = `!w:complex r:real^1 t:real^1 R.
    R + norm w + &1 <= drop r
    ==> R < norm(w + Cx(drop r) * cexp(ii * Cx(drop t)))`;;

let POLAR_FUBINI_SWAP = `!f:complex->complex w.
     f continuous_on (:complex) /\
     f differentiable_on (:complex) /\
     (!h. (\z. frechet_derivative f (at z) h) continuous_on (:complex)) /\
     bounded (support (+) f (:complex))
     ==>
     integral {r:real^1 | &0 <= drop r}
       (\r. integral (interval[vec 0, lift(&2 * pi)])
              (\t. frechet_derivative f
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t))))) =
     integral (interval[vec 0, lift(&2 * pi)])
       (\t. integral {r:real^1 | &0 <= drop r}
              (\r. frechet_derivative f
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t)))))`;;

(* Full polar decomposition: converts 2D dbar integral to constant           *)
(* angular integral. Combines FUBINI_POLAR + INNER_INTEGRAL_SIMPLIFY +       *)
(* Fubini swap + RADIAL_INTEGRAL_NEG_FW.                                     *)

let POLAR_INTEGRAL_DECOMPOSITION = `!f:complex->complex w.
     f differentiable_on (:complex) /\
     (!h. (\z. frechet_derivative f (at z) h) continuous_on (:complex)) /\
     bounded (support (+) f (:complex))
     ==> integral (:complex) (\z. wirtinger_dbar f (w + z) / z) =
         inv(Cx(&2)) *
         integral (interval[vec 0:real^1, lift(&2 * pi)]) (\t:real^1. --(f w))`;;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for the Pompeiu formula.                                    *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_CONST_2PI = `!c:complex.
     integral (interval[vec 0:real^1, lift(&2 * pi)]) (\t. c) =
     Cx(&2 * pi) * c`;;

let INV_TWO_TIMES_TWO_PI = `inv(Cx(&2)) * Cx(&2 * pi) = Cx(pi)`;;

(* ------------------------------------------------------------------------- *)
(* The Pompeiu formula: Cauchy transform inverts dbar.                       *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_TRANSFORM_INVERTS_DBAR = `!f:complex->complex w.
        f differentiable_on (:complex) /\
        (!h. (\z. frechet_derivative f (at z) h) continuous_on (:complex)) /\
        bounded (support (+) f (:complex))
        ==> integral (:complex)
              (\z. wirtinger_dbar f z / (z - w)) = --(Cx pi * f w)`;;

(* ========================================================================= *)
(* Hermite cutoff infrastructure for smooth extension.                       *)
(* ========================================================================= *)

let PIECEWISE_HAS_DERIVATIVE_LOCAL = `!(f:real^M->real^N) g ef f' z d0.
    &0 < d0 /\
    (f has_derivative f') (at z) /\
    (g has_derivative f') (at z) /\
    f z = g z /\
    (!y:real^M. norm(y - z) < d0 ==> ef y = f y \/ ef y = g y) /\
    ef z = f z
    ==> (ef has_derivative f') (at z)`;;

let PIECEWISE_HAS_REAL_DERIVATIVE_LOCAL = `!f g ef f' x d0.
    &0 < d0 /\
    (f has_real_derivative f') (atreal x) /\
    (g has_real_derivative f') (atreal x) /\
    f x = g x /\
    (!y. abs(y - x) < d0 ==> ef y = f y \/ ef y = g y) /\
    ef x = f x
    ==> (ef has_real_derivative f') (atreal x)`;;

let hermite_cutoff = new_definition
 `hermite_cutoff (t:real) =
    if t <= &0 then &1
    else if &1 <= t then &0
    else &2 * t pow 3 - &3 * t pow 2 + &1`;;

let hermite_cutoff_deriv = new_definition
 `hermite_cutoff_deriv (t:real) =
    if t <= &0 then &0
    else if &1 <= t then &0
    else &6 * t pow 2 - &6 * t`;;


let HAS_REAL_DERIVATIVE_HERMITE_INTERIOR = `!t. &0 < t /\ t < &1
       ==> (hermite_cutoff has_real_derivative (&6 * t pow 2 - &6 * t))
           (atreal t)`;;

let HAS_REAL_DERIVATIVE_HERMITE_LEFT = `!t. t < &0
       ==> (hermite_cutoff has_real_derivative (&0)) (atreal t)`;;

let HAS_REAL_DERIVATIVE_HERMITE_RIGHT = `!t. &1 < t
       ==> (hermite_cutoff has_real_derivative (&0)) (atreal t)`;;

let HAS_REAL_DERIVATIVE_HERMITE_AT_0 = `(hermite_cutoff has_real_derivative (&0)) (atreal (&0))`;;

let HAS_REAL_DERIVATIVE_HERMITE_AT_1 = `(hermite_cutoff has_real_derivative (&0)) (atreal (&1))`;;

let HAS_REAL_DERIVATIVE_HERMITE_EXPLICIT = `!t. (hermite_cutoff has_real_derivative hermite_cutoff_deriv t) (atreal t)`;;

let POLY_CONTINUOUS_REAL1 = `(\x:real^1. lift(&6 * drop x pow 2 - &6 * drop x)) continuous_on s`;;

let HERMITE_CUTOFF_DERIV_CONTINUOUS = `(lift o hermite_cutoff_deriv o drop) continuous_on (:real^1)`;;

let HERMITE_CUTOFF_DIFFERENTIABLE = `!x:real^1. (lift o hermite_cutoff o drop) differentiable (at x)`;;

let HERMITE_CUTOFF_DIFFERENTIABLE_ON = `!s. (lift o hermite_cutoff o drop) differentiable_on s`;;

let HERMITE_CUTOFF_CONTINUOUS = `(lift o hermite_cutoff o drop) continuous_on (:real^1)`;;

(* Chain rule for hermite_cutoff composed with phi(z) = (norm z^2 - R^2)/c   *)
let HERMITE_CUTOFF_CHI_HAS_DERIVATIVE = `!R c (z:complex).
     &0 < c
     ==> ((\z'. lift(hermite_cutoff((norm z' pow 2 - R pow 2) / c)))
          has_derivative
          (\h:complex. lift(hermite_cutoff_deriv((norm z pow 2 - R pow 2) / c) *
                            (&2 * (z dot h)) / c))) (at z)`;;

(* Helper lemmas for continuity of composed functions                        *)
let HERMITE_CUTOFF_LE_0 = `!t. t <= &0 ==> hermite_cutoff t = &1`;;

let HERMITE_CUTOFF_GE_1 = `!t. &1 <= t ==> hermite_cutoff t = &0`;;

let HERMITE_CUTOFF_NONNEG = `!t. &0 <= hermite_cutoff t`;;

(* ========================================================================= *)
(* C^1 extension from open sets: weaken f differentiable_on (:complex) to    *)
(* f differentiable_on u for an open set u containing the compact set K.     *)
(* Approach: cover K by finitely many balls inside u, build C^1 ball bumps,  *)
(* sum them, compose with hermite_cutoff to get a C^1 cutoff chi = 1 on K    *)
(* with support inside u, then ef = chi * f extends to all of C.             *)
(* ========================================================================= *)

(* Shifted version: derivative of hermite_cutoff((|w-a|^2 - R^2)/c)          *)
let HERMITE_CUTOFF_SHIFTED_HAS_DERIVATIVE = `!a:complex R c (z:complex).
     &0 < c
     ==> ((\w. lift(hermite_cutoff((norm(w - a) pow 2 - R pow 2) / c)))
          has_derivative
          (\h:complex. lift(hermite_cutoff_deriv
               ((norm(z - a) pow 2 - R pow 2) / c) *
               (&2 * ((z - a) dot h)) / c))) (at z)`;;

(* Continuity of shifted phi                                                 *)
let PHI_SHIFTED_CONTINUOUS_ON = `!a:complex c R s. &0 < c ==>
    (\z. lift((norm(z - a) pow 2 - R pow 2) / c)) continuous_on s`;;

(* Continuity of hcd(shifted phi) and hc(shifted phi)                        *)
let HCD_SHIFTED_CONTINUOUS_ON = `!a:complex c R s. &0 < c ==>
    (\z. lift(hermite_cutoff_deriv((norm(z - a) pow 2 - R pow 2) / c)))
    continuous_on s`;;

let HC_SHIFTED_CONTINUOUS_ON = `!a:complex c R s. &0 < c ==>
    (\z. lift(hermite_cutoff((norm(z - a) pow 2 - R pow 2) / c)))
    continuous_on s`;;

(* ========================================================================= *)
(* C^1 extension from open sets.                                             *)
(* Given compact K in open u, extend C^1 function on u to C^1 on all of C    *)
(* with compact support inside u. Uses finite ball cover + hermite cutoff.   *)
(* ========================================================================= *)

let SMOOTH_EXTENSION_FROM_OPEN = `!f:complex->complex u (K:complex->bool).
    compact K /\ open u /\ K SUBSET u /\
    f differentiable_on u /\
    (!h:complex. (\z. frechet_derivative f (at z) h) continuous_on u)
    ==> ?ef:complex->complex.
        ef differentiable_on (:complex) /\
        (!h:complex. (\z. frechet_derivative ef (at z) h)
          continuous_on (:complex)) /\
        bounded(support (+) ef (:complex)) /\
        (!z. z IN K ==> ef z = f z)`;;

(* ========================================================================= *)
(* Product-space absolute integrability for the Cauchy kernel integrand.     *)
(* Factored out from FUBINI_PATH_AREA to expose integrability separately.    *)
(* Does NOT need simple_path or pathfinish = pathstart.                      *)
(* ========================================================================= *)

let ABSOLUTELY_INTEGRABLE_CAUCHY_PATH_PRODUCT = `!u:complex->complex g:real^1->complex.
        u continuous_on (:complex) /\
        bounded (support (+) u (:complex)) /\
        g absolutely_continuous_on interval[vec 0,vec 1]
        ==> (\p:real^(1,2)finite_sum.
                if fstcart p IN interval[vec 0,vec 1]
                then u(sndcart p) / (sndcart p - g(fstcart p)) *
                     vector_derivative g (at (fstcart p))
                else vec 0)
            absolutely_integrable_on (:real^(1,2)finite_sum)`;;

(* ========================================================================= *)
(* Integrability of winding_number * dbar f without simple_path.             *)
(* Derived from the Fubini product-space integrability via:                  *)
(*   Fubini abs integ -> has_integral -> integrable ->                       *)
(*   INTEGRABLE_SPIKE -> INTEGRABLE_COMPLEX_LMUL_EQ                          *)
(* ========================================================================= *)

let INTEGRABLE_WINDING_DBAR_PRODUCT = `!f:complex->complex g:real^1->complex.
        (\z. wirtinger_dbar f z) continuous_on (:complex) /\
        bounded (support (+) (wirtinger_dbar f) (:complex)) /\
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g
        ==> (\z. Cx(Re(winding_number(g,z))) *
              wirtinger_dbar f z) integrable_on (:complex)`;;

(* ========================================================================= *)
(* Most general Gauss-Green formula: no simple_path, local C^1.              *)
(* Uses smooth extension + Cauchy transform + Fubini.                        *)
(* ========================================================================= *)

let COMPLEX_GREEN_ALT = `!f:complex->complex g u.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g /\
        open u /\
        inside(path_image g) UNION path_image g SUBSET u /\
        f differentiable_on u /\
        (!h:complex. (\z. frechet_derivative f (at z) h) continuous_on u)
        ==> (\z. Cx(Re(winding_number(g,z))) *
                 wirtinger_dbar f z) integrable_on (:complex) /\
            f path_integrable_on g /\
            Cx(inv(&2)) / ii * path_integral g f =
            integral (:complex)
              (\z. Cx(Re(winding_number(g,z))) *
                   wirtinger_dbar f z)`;;

(* Relational form: replaces Cx(Re(winding_number)) with winding_number      *)
(* (they agree a.e. since winding_number is integer off path_image g).       *)
let COMPLEX_GREEN = `!f:complex->complex g u.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g /\
        open u /\
        inside(path_image g) UNION path_image g SUBSET u /\
        f differentiable_on u /\
        (!h:complex. (\z. frechet_derivative f (at z) h) continuous_on u)
        ==> (\z. winding_number(g,z) * wirtinger_dbar f z)
            integrable_on (:complex) /\
            f path_integrable_on g /\
            path_integral g f =
            Cx(&2) * ii *
            integral (:complex)
                     (\z. winding_number(g,z) * wirtinger_dbar f z)`;;

(* Path integral of cnj for absolutely continuous closed curves.              *)
(* General form: path_integral = Cx(&2)*ii * integral_inside(wn).            *)
let HAS_PATH_INTEGRAL_CNJ = `!g:real^1->complex.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g
        ==> cnj path_integrable_on g /\
            path_integral g cnj =
            Cx(&2) * ii *
            integral (inside(path_image g))
                     (\z. winding_number(g,z))`;;

(* Gauss-Green for cnj: integral of wirtinger_dbar cnj = 1 gives area.       *)
let COMPLEX_GREEN_CNJ = `!g. g absolutely_continuous_on interval[vec 0,vec 1] /\
       pathfinish g = pathstart g /\
       (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1))
       ==> (cnj has_path_integral
            Cx(&2) * ii * Cx(measure(inside(path_image g)))) g`;;

(* Cauchy's theorem for identity (no wn hypothesis, closed path only).       *)
let HAS_PATH_INTEGRAL_I_CLOSED = `!g:real^1->complex.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g
        ==> (I has_path_integral Cx(&0)) g`;;

(* Cauchy's theorem for the identity: wirtinger_dbar I = 0.                  *)
(* Trivial corollary of HAS_PATH_INTEGRAL_I_CLOSED (extra wn hyp unused).   *)
let COMPLEX_GREEN_I = `!g. g absolutely_continuous_on interval[vec 0,vec 1] /\
       pathfinish g = pathstart g /\
       (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1))
       ==> (I has_path_integral Cx(&0)) g`;;

(* Complex area formula: measure of inside from path integral of cnj.        *)
let COMPLEX_GREEN_AREA = `!g. g absolutely_continuous_on interval[vec 0,vec 1] /\
       pathfinish g = pathstart g /\
       (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1))
       ==> cnj path_integrable_on g /\
           Cx(measure(inside(path_image g))) =
           --ii / Cx(&2) * path_integral g cnj`;;

(* Orientation-free complex area formula for simple closed curves.           *)
(* Uses COMPLEX_GREEN_INSIDE and case split on wn=+1/-1.                     *)
let COMPLEX_GREEN_AREA_ABS = `!g:real^1->complex.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        simple_path g /\ pathfinish g = pathstart g
        ==> cnj path_integrable_on g /\
            measure(inside(path_image g)) =
            norm(path_integral g cnj) / &2`;;

(* ------------------------------------------------------------------------- *)
(* Real Green's theorem (curl form) and real area formulas.                  *)
(* ------------------------------------------------------------------------- *)

(* Green's theorem in classical curl form:                                   *)
(*   integral(f2 dx + f1 dy) = integral(df1/dx - df2/dy) dA                  *)
(* Expands wirtinger_dbar integral into explicit partial derivatives.        *)
(* Statement uses real^2, basis 1, basis 2 to avoid complex paraphernalia.   *)
(* Helper lemmas (green_theorem_real, wirtinger_dbar_2i_im, linearity)       *)
(* are localized inside the proof.                                           *)
let GREEN_THEOREM_CURL = `!f:real^2->real^2 g u.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g /\
        (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1)) /\
        open u /\
        inside(path_image g) UNION path_image g SUBSET u /\
        f differentiable_on u /\
        (!h:real^2. (\z. frechet_derivative f (at z) h) continuous_on u)
        ==> (\z. lift(frechet_derivative f (at z) (basis 1) $1 -
                      frechet_derivative f (at z) (basis 2) $2))
            integrable_on inside(path_image g) /\
            (\t. lift(f(g t)$2 * vector_derivative g (at t) $1 +
                      f(g t)$1 * vector_derivative g (at t) $2))
            integrable_on interval[vec 0,vec 1] /\
            integral (interval[vec 0,vec 1])
              (\t. lift(f(g t)$2 * vector_derivative g (at t) $1 +
                        f(g t)$1 * vector_derivative g (at t) $2)) =
            integral (inside(path_image g))
              (\z. lift(frechet_derivative f (at z) (basis 1) $1 -
                        frechet_derivative f (at z) (basis 2) $2))`;;

(* De-complexified area formula: integral of x*dy = area (x*y' form).        *)
let GREEN_AREA = `!g. g absolutely_continuous_on interval[vec 0,vec 1] /\
       pathfinish g = pathstart g /\
       (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1))
       ==> (\t. lift(g t $1 * vector_derivative g (at t) $2))
           integrable_on interval[vec 0,vec 1] /\
           integral (interval[vec 0,vec 1])
             (\t. lift(g t $1 * vector_derivative g (at t) $2)) =
           lift(measure(inside(path_image g)))`;;

(* De-complexified area formula: integral of y*dx = -area (x'*y form).       *)
let GREEN_AREA_ALT = `!g. g absolutely_continuous_on interval[vec 0,vec 1] /\
       pathfinish g = pathstart g /\
       (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1))
       ==> (\t. lift(vector_derivative g (at t) $1 * g t $2))
           integrable_on interval[vec 0,vec 1] /\
           integral (interval[vec 0,vec 1])
             (\t. lift(vector_derivative g (at t) $1 * g t $2)) =
           --lift(measure(inside(path_image g)))`;;

(* Orientation-free real area formula: x*dy form.                            *)
(* For wn=+1 uses GREEN_AREA; for wn=-1 derives from componentwise           *)
(* extraction of cnj and I path integrals.                                   *)
let GREEN_AREA_ABS = `!g:real^1->complex.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        simple_path g /\ pathfinish g = pathstart g
        ==> (\t. lift(g t $1 * vector_derivative g (at t) $2))
            integrable_on interval[vec 0,vec 1] /\
            norm(integral (interval[vec 0,vec 1])
              (\t. lift(g t $1 * vector_derivative g (at t) $2))) =
            measure(inside(path_image g))`;;

(* Orientation-free real area formula: y*dx form.                            *)
let GREEN_AREA_ABS_ALT = `!g:real^1->complex.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        simple_path g /\ pathfinish g = pathstart g
        ==> (\t. lift(vector_derivative g (at t) $1 * g t $2))
            integrable_on interval[vec 0,vec 1] /\
            norm(integral (interval[vec 0,vec 1])
              (\t. lift(vector_derivative g (at t) $1 * g t $2))) =
            measure(inside(path_image g))`;;
