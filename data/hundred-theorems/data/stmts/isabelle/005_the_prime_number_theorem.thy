(*
  File:       Prime Number Theorem.thy
  Authors:    Manuel Eberl (TU München), Larry Paulson (University of Cambridge)

  A proof of the Prime Number Theorem and some related properties
*)
section \<open>The Prime Number Theorem\<close>
theory Prime_Number_Theorem
imports 
  Newman_Ingham_Tauberian
  Prime_Counting_Functions
begin

(*<*)
unbundle prime_counting_syntax
(*>*)

subsection \<open>Constructing Newman's function\<close>

text \<open>
  Starting from Mertens' first theorem, i.\,e.\ $\mathfrak M(x) = \ln x + O(1)$, we now 
  want to derive that $\mathfrak M(x) = \ln x + c + o(1)$. This result is considerably stronger
  and it implies the Prime Number Theorem quite directly.

  In order to do this, we define the Dirichlet series
  \[f(s) = \sum_{n=1}^\infty \frac{\mathfrak{M}(n)}{n^s}\ .\]
  We will prove that this series extends meromorphically to $\mathfrak{R}(s)\geq 1$ and
  apply Ingham's theorem to it (after we subtracted its pole at $s = 1$).
\<close>
definition fds_newman where
  "fds_newman = fds (\<lambda>n. complex_of_real (\<MM> n))"

lemma fds_nth_newman:
  "fds_nth fds_newman n = of_real (\<MM> n)"
  by sorry

lemma norm_fds_nth_newman:
  "norm (fds_nth fds_newman n) = \<MM> n"
  by sorry

text \<open>
  The Dirichlet series $f(s) + \zeta'(s)$ has the coefficients $\mathfrak{M}(n) - \ln n$,
  so by Mertens' first theorem, $f(s) + \zeta'(s)$ has bounded coefficients.
\<close>
lemma bounded_coeffs_newman_minus_deriv_zeta:
  defines "f \<equiv> fds_newman + fds_deriv fds_zeta"
  shows   "Bseq (\<lambda>n. fds_nth f n)"
  by sorry

text \<open>
  A Dirichlet series with bounded coefficients converges for all $s$ with
  $\mathfrak{R}(s)>1$ and so does $\zeta'(s)$, so we can conclude that $f(s)$ does as well.
\<close>
lemma abs_conv_abscissa_newman: "abs_conv_abscissa fds_newman \<le> 1"
  and conv_abscissa_newman:     "conv_abscissa fds_newman \<le> 1"
  by sorry

text \<open>
  We now change the order of summation to obtain an alternative form of $f(s)$ in terms of a 
  sum of Hurwitz $\zeta$ functions.
\<close>
lemma eval_fds_newman_conv_infsetsum:
  assumes s: "Re s > 1"
  shows   "eval_fds fds_newman s = (\<Sum>\<^sub>ap | prime p. (ln (real p) / real p) * hurwitz_zeta p s)"
          "(\<lambda>p. ln (real p) / real p * hurwitz_zeta p s) abs_summable_on {p. prime p}"
  by sorry


text \<open>
  We now define a meromorphic continuation of $f(s)$ on $\mathfrak{R}(s) > \frac{1}{2}$.

  To construct $f(s)$, we express it as
  \[f(s) = \frac{1}{z-1}\left(\bar f(s) - \frac{\zeta'(s)}{\zeta(s)}\right)\ ,\]
  where $\bar f(s)$ (which we shall call \<open>pre_newman\<close>) is a function that is analytic on
  $\Re(s) > \frac{1}{2}$, which can be shown fairly easily using the Weierstra{\ss} M test.
  
  $\zeta'(s)/\zeta(s)$ is meromorphic except for a single pole at $s = 1$ and one $k$-th order
  pole for any $k$-th order zero of $\zeta$, but for the Prime Number Theorem, we are only
  concerned with the area $\mathfrak{R}(s) \geq 1$, where $\zeta$ does not have any zeros.

  Taken together, this means that $f(s)$ is analytic for $\mathfrak{R}(s)\geq 1$ except for a
  double pole at $s = 1$, which we will take care of later.
\<close>

context
  fixes A :: "nat \<Rightarrow> complex \<Rightarrow> complex" and B :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  defines "A \<equiv> (\<lambda>p s. (s - 1) * pre_zeta (real p) s - 
                         of_nat p / (of_nat p powr s * (of_nat p powr s - 1)))"
  defines "B \<equiv> (\<lambda>p s. of_real (ln (real p)) / of_nat p * A p s)"
begin

definition pre_newman :: "complex \<Rightarrow> complex" where
  "pre_newman s = (\<Sum>p. if prime p then B p s else 0)"

definition newman where "newman s = 1 / (s - 1) * (pre_newman s - deriv zeta s / zeta s)"

text \<open>
  The sum used in the definition of \<open>pre_newman\<close> converges uniformly on any disc within the
  half-space with $\mathfrak{R}(s) > \frac{1}{2}$ by the Weierstra{\ss} M test.
\<close>
lemma uniform_limit_pre_newman:
  assumes r: "r \<ge> 0" "Re s - r > 1 / 2"
  shows "uniform_limit (cball s r)
           (\<lambda>n s. \<Sum>p<n. if prime p then B p s else 0) pre_newman at_top"
  by sorry

lemma sums_pre_newman: "Re s > 1 / 2 \<Longrightarrow> (\<lambda>p. if prime p then B p s else 0) sums pre_newman s"
  by sorry

lemma analytic_pre_newman [THEN analytic_on_subset, analytic_intros]:
  "pre_newman analytic_on {s. Re s > 1 / 2}"
  by sorry

lemma holomorphic_pre_newman [holomorphic_intros]:
  "X \<subseteq> {s. Re s > 1 / 2} \<Longrightarrow> pre_newman holomorphic_on X"
  by sorry

lemma eval_fds_newman:
  assumes s: "Re s > 1"
  shows   "eval_fds fds_newman s = newman s"
  by sorry

end

text \<open>
  Next, we shall attempt to get rid of the pole by subtracting suitable multiples of $\zeta(s)$
  and $\zeta'(s)$. To this end, we shall first prove the following alternative definition of 
  $\zeta'(s)$:
\<close>
lemma deriv_zeta_eq':
  assumes "0 < Re s" "s \<noteq> 1"
  shows "deriv zeta s = deriv (\<lambda>z. pre_zeta 1 z * (z - 1)) s / (s - 1) -
                          (pre_zeta 1 s * (s - 1) + 1) / (s - 1)\<^sup>2"
    (is "_ = ?rhs")
  by sorry

text \<open>
  From this, it follows that $(s - 1) \zeta'(s) - \zeta'(s) / \zeta(s)$ is analytic 
  for $\mathfrak{R}(s) \geq 1$:
\<close>
lemma analytic_zeta_derivdiff:
  obtains a where
    "(\<lambda>z. if z = 1 then a else (z - 1) * deriv zeta z - deriv zeta z / zeta z)
          analytic_on {s. Re s \<ge> 1}" 
  by sorry

text \<open>
  Finally, $f(s) + \zeta'(s) + c\zeta(s)$ is analytic.
\<close>
lemma analytic_newman_variant:
  obtains c a where
     "(\<lambda>z. if z = 1 then a else newman z + deriv zeta z + c * zeta z) analytic_on {s. Re s \<ge> 1}"
  by sorry


subsection \<open>The asymptotic expansion of \<open>\<MM>\<close>\<close>

text \<open>
  Our next goal is to show the key result that $\mathfrak{M}(x) = \ln n + c + o(1)$.

  As a first step, we invoke Ingham's Tauberian theorem on the function we have
  just defined and obtain that the sum
  \[\sum\limits_{n=1}^\infty \frac{\mathfrak{M}(n) - \ln n + c}{n}\]
  exists.
\<close>
lemma mertens_summable:
  obtains c :: real where "summable (\<lambda>n. (\<MM> n - ln n + c) / n)"
  by sorry

text \<open>
  Next, we prove a lemma given by Newman stating that if the sum $\sum a_n / n$ exists and
  $a_n + \ln n$ is nondecreasing, then $a_n$ must tend to 0. Unfortunately, the proof is
  rather tedious, but so is the paper version by Newman.
\<close>
lemma sum_goestozero_lemma:
  fixes d::real
  assumes d: "\<bar>\<Sum>i = M..N. a i / i\<bar> < d" and le: "\<And>n. a n + ln n \<le> a (Suc n) + ln (Suc n)"
      and "0 < M" "M < N"
    shows "a M \<le> d * N / (real N - real M) + (real N - real M) / M \<and>
          -a N \<le> d * N / (real N - real M) + (real N - real M) / M"
  by sorry

proposition sum_goestozero_theorem:
  assumes summ: "summable (\<lambda>i. a i / i)"
      and le:   "\<And>n. a n + ln n \<le> a (Suc n) + ln (Suc n)"
    shows "a \<longlonglongrightarrow> 0"
  by sorry


text \<open>
  This leads us to the main intermediate result:
\<close>
lemma Mertens_convergent: "convergent (\<lambda>n::nat. \<MM> n - ln n)"
  by sorry

corollary \<MM>_minus_ln_limit:
  obtains c where "((\<lambda>x::real. \<MM> x - ln x) \<longlongrightarrow> c) at_top"
  by sorry


subsection \<open>The asymptotics of the prime-counting functions\<close>

text \<open>
  We will now use the above result to prove the asymptotics of the prime-counting functions
  $\vartheta(x) \sim x$, $\psi(x) \sim x$, and $\pi(x) \sim x / \ln x$. The last of these is 
  typically called the Prime Number Theorem, but since these functions can be expressed in terms 
  of one another quite easily, knowing the asymptotics of any of them immediately gives the 
  asymptotics of the other ones.

  In this sense, all of the above are equivalent formulations of the Prime Number Theorem.
  The one we shall tackle first, due to its strong connection to the $\mathfrak{M}$ function, is
  $\vartheta(x) \sim x$.

  We know that $\mathfrak{M}(x)$ has the asymptotic expansion
  $\mathfrak{M}(x) = \ln x + c + o(1)$. We also know that
  \[\vartheta(x) = x\mathfrak{M}(x) - \int\nolimits_2^x \mathfrak{M}(t) \,\mathrm{d}t\ .\]
  Substituting in the above asymptotic equation, we obtain:
  \begin{align*}
  \vartheta(x) &= x\ln x + cx + o(x) - \int\nolimits_2^x \ln t + c + o(1) \,\mathrm{d}t\\
            &= x\ln x + cx + o(x) - (x\ln x - x + cx + o(x))\\
            &= x + o(x)
  \end{align*}
  In conclusion, $\vartheta(x) \sim x$.
\<close>
theorem \<theta>_asymptotics: "\<theta> \<sim>[at_top] (\<lambda>x. x)"
  by sorry

text \<open>
  The various other forms of the Prime Number Theorem follow as simple corollaries.
\<close>
corollary \<psi>_asymptotics: "\<psi> \<sim>[at_top] (\<lambda>x. x)"
  by sorry
  
corollary prime_number_theorem: "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
  by sorry

corollary ln_\<pi>_asymptotics: "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] ln"
  by sorry

corollary \<pi>_ln_\<pi>_asymptotics: "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
  by sorry

corollary nth_prime_asymptotics: "(\<lambda>n. real (nth_prime n)) \<sim>[at_top] (\<lambda>n. real n * ln (real n))"
  by sorry


text \<open>
  The following versions use a little less notation.
\<close>
corollary prime_number_theorem': "((\<lambda>x. \<pi> x / (x / ln x)) \<longlongrightarrow> 1) at_top"
  by sorry

corollary prime_number_theorem'':
  "(\<lambda>x. card {p. prime p \<and> real p \<le> x}) \<sim>[at_top] (\<lambda>x. x / ln x)"
  by sorry

corollary prime_number_theorem''':
  "(\<lambda>n. card {p. prime p \<and> p \<le> n}) \<sim>[at_top] (\<lambda>n. real n / ln (real n))"
  by sorry

(*<*)
unbundle no prime_counting_syntax
(*>*)

end