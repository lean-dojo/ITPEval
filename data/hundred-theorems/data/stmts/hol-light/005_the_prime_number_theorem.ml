(* ========================================================================= *)
(* "Second proof" of Prime Number Theorem from Newman's book.                *)
(* ========================================================================= *)

needs "Multivariate/cauchy.ml";;
needs "Library/pocklington.ml";;
needs "Examples/mangoldt.ml";;

prioritize_real();;
prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* A few miscelleneous lemmas.                                               *)
(* ------------------------------------------------------------------------- *)

let LT_NORM_CPOW_NUM = `!n s. &0 < Re s /\ 2 <= n ==> &1 < norm(Cx(&n) cpow s)`;;

let CPOW_NUM_NE_1 = `!n s. &0 < Re s /\ 2 <= n ==> ~(Cx(&n) cpow s = Cx(&1))`;;

let FINITE_ATMOST = `!P n. FINITE {m:num | P m /\ m <= n}`;;

let PRIME_ATMOST_ALT = `{p | prime p /\ p <= n} = {p | p IN 1..n /\ prime p}`;;

(* ------------------------------------------------------------------------- *)
(* An auxiliary zeta function that's analytic in the right halfplane.        *)
(* ------------------------------------------------------------------------- *)

let nearzeta = new_definition
 `nearzeta n s = infsum (from n)
                        (\m. (s - Cx(&1)) / Cx(&m) cpow s -
                              (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                               Cx(&1) / Cx(&(m+1)) cpow (s - Cx(&1))))`;;

(* ------------------------------------------------------------------------- *)
(* The actual zeta function, with analyticity of z_n(s) - 1/(s - 1)^{n-1}    *)
(* ------------------------------------------------------------------------- *)

let genzeta = new_definition
 `genzeta n s = if s = Cx(&1) then complex_derivative (nearzeta n) (Cx(&1))
                else (nearzeta n s + Cx(&1) / Cx(&n) cpow (s - Cx(&1))) /
                     (s - Cx(&1))`;;

let zeta = new_definition
 `zeta s = genzeta 1 s`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about convergence and analyticity of the series.                   *)
(* ------------------------------------------------------------------------- *)

let NEARZETA_BOUND_LEMMA = `!s n. ~(n = 0) /\ &0 <= Re s + &1
         ==> norm((s - Cx(&1)) / Cx(&n) cpow s -
                  (Cx(&1) / Cx(&n) cpow (s - Cx(&1)) -
                   Cx(&1) / Cx(&(n + 1)) cpow (s - Cx(&1)))) <=
             norm(s * (s - Cx(&1)) / Cx(&n) cpow (s + Cx(&1)))`;;

let NORM_CPOW_LOWERBOUND = `!m s n. &m <= Re s /\ ~(n = 0) ==> &n pow m <= norm(Cx(&n) cpow s)`;;

let ZETATERM_BOUND = `!s n m. &m <= Re s /\ ~(n = 0)
           ==> norm(Cx(&1) / Cx(&n) cpow s) <= inv(&n pow m)`;;

let ZETA_CONVERGES_LEMMA = `!n s. &2 <= Re s ==> summable (from n) (\m. Cx(&1) / Cx(&m) cpow s)`;;

let ZETADIFF_CONVERGES = `!n s. &0 < Re(s)
         ==> ((\m. Cx(&1) / Cx(&m) cpow s - Cx(&1) / Cx(&(m + 1)) cpow s)
              sums Cx(&1) / Cx(&n) cpow s) (from n)`;;

let NEARZETA_CONVERGES_LEMMA = `!n s. &1 <= Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`;;

let GENZETA_CONVERGES = `!n s. &1 < Re s
         ==> ((\m. Cx(&1) / Cx(&m) cpow s) sums genzeta n s) (from n)`;;

let ZETA_CONVERGES = `!s. &1 < Re s
       ==> ((\n. Cx(&1) / Cx(&n) cpow s) sums zeta(s)) (from 1)`;;

(* ------------------------------------------------------------------------- *)
(* We need the series for the derivative at one stage, so do this now.       *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DERIVATIVE_ZETA_CONVERGES = `!s. &1 < Re s
       ==> ((\n. --clog(Cx(&n)) / Cx(&n) cpow s) sums
            complex_derivative zeta s) (from 1)`;;

(* ------------------------------------------------------------------------- *)
(* The zeta function is actually analytic on a larger set.                   *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_NEARZETA_LEMMA = `!n. 1 <= n
       ==> ?g g'. !s. s IN {s | Re(s) > &0}
                      ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                           (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                            Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
                           sums g s) (from n) /\
                           ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) /
                                 Cx(&m) cpow s -
                                 (clog(Cx(&(m + 1))) /
                                  Cx(&(m + 1)) cpow (s - Cx(&1)) -
                                  clog(Cx(&m)) /
                                  Cx(&m) cpow (s - Cx(&1))))
                            sums g' s) (from n) /\
                       (g has_complex_derivative g' s) (at s)`;;

let HOLOMORPHIC_NEARZETA_STRONG = `!n s. 1 <= n /\ &0 < Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
              (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
               Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums (nearzeta n s)) (from n) /\
              ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) /
                    Cx(&m) cpow s -
                    (clog(Cx(&(m + 1))) /
                     Cx(&(m + 1)) cpow (s - Cx(&1)) -
                     clog(Cx(&m)) /
                     Cx(&m) cpow (s - Cx(&1))))
               sums (complex_derivative(nearzeta n) s)) (from n) /\
          ((nearzeta n) has_complex_derivative
           complex_derivative(nearzeta n) s) (at s)`;;

let NEARZETA_CONVERGES = `!n s. &0 < Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`;;

let SUMS_COMPLEX_DERIVATIVE_NEARZETA = `!n s. 1 <= n /\ &0 < Re s
         ==> ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) / Cx(&m) cpow s -
                    (clog(Cx(&(m + 1))) / Cx(&(m + 1)) cpow (s - Cx(&1)) -
                     clog(Cx(&m)) / Cx(&m) cpow (s - Cx(&1)))) sums
            (complex_derivative (nearzeta n) s)) (from n)`;;

let HOLOMORPHIC_NEARZETA = `!n. 1 <= n ==> (nearzeta n) holomorphic_on {s | Re(s) > &0}`;;

let COMPLEX_DIFFERENTIABLE_NEARZETA = `!n s. 1 <= n /\ &0 < Re s ==> (nearzeta n) complex_differentiable (at s)`;;

let NEARZETA_1 = `!n. 1 <= n ==> nearzeta n (Cx(&1)) = Cx(&0)`;;

let HOLOMORPHIC_ZETA = `zeta holomorphic_on {s | Re(s) > &0 /\ ~(s = Cx(&1))}`;;

let COMPLEX_DIFFERENTIABLE_AT_ZETA = `!s. &0 < Re s /\ ~(s = Cx(&1))
       ==> zeta complex_differentiable at s`;;

(* ------------------------------------------------------------------------- *)
(* Euler product formula. Nice proof from Ahlfors' book avoiding any         *)
(* messing round with the geometric series.                                  *)
(* ------------------------------------------------------------------------- *)

let SERIES_DIVISORS_LEMMA = `!x p l k.
      ((\n. x(p * n)) sums l) k
      ==> ~(p = 0) /\
          (!n. (p * n) IN k <=> n IN k)
          ==> (x sums l) {n | n IN k /\ p divides n}`;;

let EULER_PRODUCT_LEMMA = `!s ps. &1 < Re s /\ FINITE ps /\ (!p. p IN ps ==> prime p)
          ==> ((\n. Cx(&1) / Cx(&n) cpow s) sums
               (cproduct ps (\p. Cx(&1) - inv(Cx(&p) cpow s)) * zeta s))
       {n | 1 <= n /\ !p. prime p /\ p divides n ==> ~(p IN ps)}`;;

let SUMMABLE_SUBZETA = `!s t. &1 < Re s /\ ~(0 IN t)
         ==> summable t (\n. Cx (&1) / Cx (&n) cpow s)`;;

let EULER_PRODUCT_MULTIPLY = `!s. &1 < Re s
       ==> ((\n. cproduct {p | prime p /\ p <= n}
                          (\p. Cx(&1) - inv(Cx(&p) cpow s)) * zeta s)
            --> Cx(&1)) sequentially`;;

let ZETA_NONZERO_LEMMA = `!s. &1 < Re s ==> ~(zeta s = Cx(&0))`;;

let EULER_PRODUCT = `!s. &1 < Re s
       ==> ((\n. cproduct {p | prime p /\ p <= n}
                          (\p. inv(Cx(&1) - inv(Cx(&p) cpow s))))
            --> zeta(s)) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Show that s = 1 is not a zero, just for tidiness.                         *)
(* ------------------------------------------------------------------------- *)

let SUMS_GAMMA = `((\n. Cx(sum(1..n) (\i. &1 / &i - (log(&(i + 1)) - log(&i))))) -->
    complex_derivative (nearzeta 1) (Cx(&1))) sequentially`;;

let ZETA_1_NZ = `~(zeta(Cx(&1)) = Cx(&0))`;;

(* ------------------------------------------------------------------------- *)
(* Lack of zeros on Re(s) >= 1. Nice proof from Bak & Newman.                *)
(* ------------------------------------------------------------------------- *)

let ZETA_MULTIPLE_BOUND = `!x y. real x /\ real y /\ &1 < Re x
       ==> &1 <= norm(zeta(x) pow 3 *
                      zeta(x + ii * y) pow 4 *
                      zeta(x + Cx(&2) * ii * y) pow 2)`;;

let ZETA_NONZERO = `!s. &1 <= Re s ==> ~(zeta s = Cx(&0))`;;

let NEARZETA_NONZERO = `!s. &1 <= Re s ==> ~(nearzeta 1 s + Cx (&1) = Cx(&0))`;;

(* ------------------------------------------------------------------------- *)
(* The logarithmic derivative of the zeta function.                          *)
(* ------------------------------------------------------------------------- *)

let NORM_CLOG_BOUND = `norm(z) <= &1 / &2 ==> norm(clog(Cx(&1) - z)) <= &2 * norm(z)`;;

let LOGZETA_EXISTS = `?logzeta logzeta'.
        !s. s IN {s | Re s > &1}
            ==> ((\p. clog(Cx(&1) - inv(Cx(&p) cpow s)))
                 sums logzeta(s))
                {p | prime p} /\
                ((\p. clog(Cx(&p)) / (Cx(&p) cpow s - Cx(&1)))
                 sums logzeta'(s))
                {p | prime p} /\
                (logzeta has_complex_derivative logzeta'(s)) (at s)`;;

let LOGZETA_PROPERTIES =
  new_specification ["logzeta"; "logzeta'"] LOGZETA_EXISTS;;

let [LOGZETA_CONVERGES; LOGZETA'_CONVERGES; HAS_COMPLEX_DERIVATIVE_LOGZETA] =
    CONJUNCTS(REWRITE_RULE[IN_ELIM_THM; FORALL_AND_THM; real_gt; TAUT
                             `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]
                          LOGZETA_PROPERTIES);;

let CEXP_LOGZETA = `!s. &1 < Re s ==> cexp(--(logzeta s)) = zeta s`;;

let HAS_COMPLEX_DERIVATIVE_ZETA = `!s. &1 < Re s ==> (zeta has_complex_derivative
                      (--(logzeta'(s)) * zeta(s))) (at s)`;;

let COMPLEX_DERIVATIVE_ZETA = `!s. &1 < Re s
       ==> complex_derivative zeta s = --(logzeta'(s)) * zeta(s)`;;

let CONVERGES_LOGZETA'' = `!s. &1 < Re s
       ==> ((\p. Cx(log(&p)) / (Cx(&p) cpow s - Cx(&1))) sums
            (--(complex_derivative zeta s / zeta s))) {p | prime p}`;;

(* ------------------------------------------------------------------------- *)
(* Some lemmas about negating a path.                                        *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_NEGATEPATH = `!g. valid_path g ==> valid_path ((--) o g)`;;

let PATHSTART_NEGATEPATH = `!g. pathstart((--) o g) = --(pathstart g)`;;

let PATHFINISH_NEGATEPATH = `!g. pathfinish((--) o g) = --(pathfinish g)`;;

let PATH_IMAGE_NEGATEPATH = `!g. path_image((--) o g) = IMAGE (--) (path_image g)`;;

let HAS_PATH_INTEGRAL_NEGATEPATH = `!g z. valid_path g /\ ((\z. f(--z)) has_path_integral (--i)) g
         ==> (f has_path_integral i) ((--) o g)`;;

let WINDING_NUMBER_NEGATEPATH = `!g z. valid_path g /\ ~(Cx(&0) IN path_image g)
         ==> winding_number((--) o g,Cx(&0)) = winding_number(g,Cx(&0))`;;

let PATH_INTEGRABLE_NEGATEPATH = `!g z. valid_path g /\ (\z. f(--z)) path_integrable_on g
         ==> f path_integrable_on ((--) o g)`;;

(* ------------------------------------------------------------------------- *)
(* Some bounding lemmas given by Newman. BOUND_LEMMA_2 is my variant since I *)
(* use a slightly different contour.                                         *)
(* ------------------------------------------------------------------------- *)

let BOUND_LEMMA_0 = `!z R. norm(z) = R
         ==> Cx(&1) / z + z / Cx(R) pow 2 = Cx(&2 * Re z / R pow 2)`;;

let BOUND_LEMMA_1 = `!z R. norm(z) = R
         ==> norm(Cx(&1) / z + z / Cx(R) pow 2) = &2 * abs(Re z) / R pow 2`;;

let BOUND_LEMMA_2 = `!R x z. Re(z) = --x /\ abs(Im(z)) = R /\ &0 <= x /\ &0 < R
           ==> norm (Cx (&1) / z + z / Cx R pow 2) <= &2 * x / R pow 2`;;

let BOUND_LEMMA_3 = `!a n. (!m. 1 <= m ==> norm(a(m)) <= &1) /\
         1 <= n /\ &1 <= Re w /\ &0 < Re z
         ==> norm(vsum(1..n) (\n. a(n) / Cx(&n) cpow (w - z)))
                  <= exp(Re(z) * log(&n)) * (&1 / &n + &1 / Re(z))`;;

let BOUND_LEMMA_4 = `!a n m. (!m. 1 <= m ==> norm(a(m)) <= &1) /\
           1 <= n /\ &1 <= Re w /\ &0 < Re z
           ==> norm(vsum(n+1..m) (\n. a(n) / Cx(&n) cpow (w + z)))
                    <= &1 / (Re z * exp(Re z * log(&n)))`;;

(* ------------------------------------------------------------------------- *)
(* Our overall bound does go to zero as N increases.                         *)
(* ------------------------------------------------------------------------- *)

let OVERALL_BOUND_LEMMA = `!d M R. &0 < d
           ==> !e. &0 < e
                   ==> ?N. !n. N <= n
                               ==> abs(&2 * pi / &n +
                                       &6 * M * R / (d * exp (d * log (&n))) +
                                       &4 * M / (R * log (&n)) pow 2) < e`;;

(* ------------------------------------------------------------------------- *)
(* Newman/Ingham analytic lemma (as in Newman's book).                       *)
(* ------------------------------------------------------------------------- *)

let NEWMAN_INGHAM_THEOREM = `!f a. (!n. 1 <= n ==> norm(a(n)) <= &1) /\
         f analytic_on {z | Re(z) >= &1} /\
         (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
         ==> !z. Re(z) >= &1
                 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`;;

(* ------------------------------------------------------------------------- *)
(* The application is to any bounded a_n, not |a_n| <= 1, so...              *)
(* ------------------------------------------------------------------------- *)

let NEWMAN_INGHAM_THEOREM_BOUND = `!f a b. &0 < b /\
           (!n. 1 <= n ==> norm(a(n)) <= b) /\
           f analytic_on {z | Re(z) >= &1} /\
           (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
           ==> !z. Re(z) >= &1
                   ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`;;

let NEWMAN_INGHAM_THEOREM_STRONG = `!f a b. (!n. 1 <= n ==> norm(a(n)) <= b) /\
           f analytic_on {z | Re(z) >= &1} /\
           (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
           ==> !z. Re(z) >= &1
                   ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`;;

(* ------------------------------------------------------------------------- *)
(* Newman's analytic function "f", re-using our "nearzeta" stuff.            *)
(* ------------------------------------------------------------------------- *)

let GENZETA_BOUND_LEMMA = `!n s m. ~(n = 0) /\ &1 < Re s /\ n + 1 <= m
           ==> sum(n..m) (\x. norm(Cx(&1) / Cx(&x) cpow s))
                <= (&1 / &n + &1 / (Re s - &1)) * exp((&1 - Re s) * log(&n))`;;

let GENZETA_BOUND = `!n s. ~(n = 0) /\ &1 < Re s
         ==> norm(genzeta n s) <=
                (&1 / &n + &1 / (Re s - &1)) * exp((&1 - Re s) * log(&n))`;;

let NEARZETA_BOUND_SHARP = `!n s. ~(n = 0) /\ &0 < Re s
         ==> norm(nearzeta n s) <=
                  norm(s * (s - Cx(&1))) *
                  (&1 / &n + &1 / Re s) / exp(Re s * log(&n))`;;

let NEARZETA_BOUND = `!n s. ~(n = 0) /\ &0 < Re s
         ==> norm(nearzeta n s)
                  <= ((norm(s) + &1) pow 3 / Re s) / exp (Re s * log (&n))`;;

let NEARNEWMAN_EXISTS = `?f. !s. s IN {s | Re(s) > &1 / &2}
           ==> ((\p. clog(Cx(&p)) / Cx(&p) * nearzeta p s -
                     clog(Cx(&p)) / (Cx(&p) cpow s * (Cx(&p) cpow s - Cx(&1))))
                sums (f s)) {p | prime p} /\
               f complex_differentiable (at s)`;;

let nearnewman = new_specification ["nearnewman"] NEARNEWMAN_EXISTS;;

let [CONVERGES_NEARNEWMAN; COMPLEX_DIFFERENTIABLE_NEARNEWMAN] =
  CONJUNCTS(REWRITE_RULE[FORALL_AND_THM; IN_ELIM_THM; real_gt;
                         TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]
                nearnewman);;

let newman = new_definition
 `newman(s) = (nearnewman(s) - (complex_derivative zeta s / zeta s)) /
              (s - Cx(&1))`;;

(* ------------------------------------------------------------------------- *)
(* Careful correlation of singularities of the various functions.            *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DERIVATIVE_ZETA = `!s. &0 < Re s /\ ~(s = Cx(&1))
       ==> complex_derivative zeta s =
                complex_derivative (nearzeta 1) s / (s - Cx(&1)) -
                (nearzeta 1 s + Cx(&1)) / (s - Cx(&1)) pow 2`;;

let ANALYTIC_ZETA_DERIVDIFF = `?a. (\z. if z = Cx(&1) then a
            else (z - Cx(&1)) * complex_derivative zeta z -
                 complex_derivative zeta z / zeta z)
       analytic_on {s | Re(s) >= &1}`;;

let ANALYTIC_NEWMAN_VARIANT = `?c a. (\z. if z = Cx(&1) then a
              else newman z + complex_derivative zeta z + c * zeta z)
         analytic_on {s | Re(s) >= &1}`;;

(* ------------------------------------------------------------------------- *)
(* Hence apply the analytic lemma.                                           *)
(* ------------------------------------------------------------------------- *)

let CONVERGES_NEWMAN_PRIME = `!s. &1 < Re s
       ==> ((\p. clog(Cx(&p)) / Cx(&p) * genzeta p s) sums newman(s))
           {p | prime p}`;;

(* ------------------------------------------------------------------------- *)
(* Now swap the order of summation in the series.                            *)
(* ------------------------------------------------------------------------- *)

let GENZETA_OFFSET = `!m n s. &1 < Re s /\ m <= n
           ==> genzeta m s - vsum(m..n) (\k. Cx(&1) / Cx(&k) cpow s) =
               genzeta (n + 1) s`;;

let NEWMAN_CONVERGES = `!s. &1 < Re s
       ==> ((\n. vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) /
                 Cx(&n) cpow s)
            sums (newman s)) (from 1)`;;

(* ------------------------------------------------------------------------- *)
(* Hence the main result of the analytic part.                               *)
(* ------------------------------------------------------------------------- *)

let MAIN_RESULT = `?c. summable (from 1)
        (\n. (vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) -
              clog(Cx(&n)) + c) / Cx(&n))`;;

(* ------------------------------------------------------------------------- *)
(* The theorem relating summability and convergence.                         *)
(* ------------------------------------------------------------------------- *)

let SUM_GOESTOZERO_LEMMA = `!a M N.
        abs(sum(M..N) (\i. a(i) / &i)) <= d
        ==> 0 < M /\ M < N /\ (!n. a(n) + log(&n) <= a(n + 1) + log(&n + &1))
            ==> a(M) <= d * &N / (&N - &M) + (&N - &M) / &M /\
                --a(N) <= d * &N / (&N - &M) + (&N - &M) / &M`;;

let SUM_GOESTOZERO_THEOREM = `!a c. ((\i. a(i) / &i) real_sums c) (from 1) /\
         (!n. a(n) + log(&n) <= a(n + 1) + log(&n + &1))
         ==> (a ---> &0) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Hence transform into the desired limit.                                   *)
(* ------------------------------------------------------------------------- *)

let MERTENS_LIMIT = `?c. ((\n. sum {p | prime p /\ p <= n} (\p. log(&p) / &p) - log(&n))
        ---> c) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Reformulate the PNT using partial summation.                              *)
(* ------------------------------------------------------------------------- *)

let PNT_PARTIAL_SUMMATION = `&(CARD {p | prime p /\ p <= n}) =
        sum(1..n)
         (\k. &k / log (&k) *
              (sum {p | prime p /\ p <= k} (\p. log (&p) / &p) -
               sum {p | prime p /\ p <= k - 1} (\p. log (&p) / &p)))`;;

let SUM_PARTIAL_LIMIT = `!f e c M.
        (!k. M <= k ==> &0 < f k) /\
        (!k. M <= k ==> f(k) <= f(k + 1)) /\
        ((\k. inv(f k)) ---> &0) sequentially /\
        (e ---> c) sequentially
        ==> ((\n. (sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
                  f(n + 1)) ---> &0) sequentially`;;

let SUM_PARTIAL_LIMIT_ALT = `!f e b c M.
        (!k. M <= k ==> &0 < f k) /\
        (!k. M <= k ==> f(k) <= f(k + 1)) /\
        ((\k. inv(f k)) ---> &0) sequentially /\
        ((\n. f(n + 1) / f n) ---> b) sequentially /\
        (e ---> c) sequentially
        ==> ((\n. (sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
                  f(n)) ---> &0) sequentially`;;

let REALLIM_NA_OVER_N = `!a. ((\n. (&n + a) / &n) ---> &1) sequentially`;;

let REALLIM_N_OVER_NA = `!a. ((\n. &n / (&n + &1)) ---> &1) sequentially`;;

let REALLIM_LOG1_OVER_LOG = `((\n. log(&n + &1) / log(&n)) ---> &1) sequentially`;;

let REALLIM_LOG_OVER_LOG1 = `((\n. log(&n) / log(&n + &1)) ---> &1) sequentially`;;

let ADHOC_BOUND_LEMMA = `!k. 1 <= k ==> abs((&k + &1) * (log(&k + &1) - log(&k)) - &1)
                  <= &2 / &k`;;

let REALLIM_MUL_SERIES = `!x y z B.
        eventually (\n. &0 < x n) sequentially /\
        eventually (\n. &0 < y n) sequentially /\
        eventually (\n. &0 < z n) sequentially /\
        ((\n. inv(z n)) ---> &0) sequentially /\
        eventually (\n. abs(sum (1..n) x / z(n)) <= B) sequentially /\
        ((\n. y(n) / x(n)) ---> &0) sequentially
        ==> ((\n. sum (1..n) y / z(n)) ---> &0) sequentially`;;

let REALLIM_MUL_SERIES_LIM = `!x y z l.
        eventually (\n. &0 < x n) sequentially /\
        eventually (\n. &0 < y n) sequentially /\
        eventually (\n. &0 < z n) sequentially /\
        ((\n. inv(z n)) ---> &0) sequentially /\
        ((\n. sum (1..n) x / z(n)) ---> l) sequentially /\
        ((\n. y(n) / x(n)) ---> &0) sequentially
        ==> ((\n. sum (1..n) y / z(n)) ---> &0) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Finally, the Prime Number Theorem!                                        *)
(* ------------------------------------------------------------------------- *)

let PNT = `((\n. &(CARD {p | prime p /\ p <= n}) / (&n / log(&n)))
    ---> &1) sequentially`;;
