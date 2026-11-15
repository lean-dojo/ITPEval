(*
  File:   Prime_Harmonic.thy
  Author: Manuel Eberl <manuel@pruvisto.org>

  A lower bound for the partial sums of the prime harmonic series, and a proof of its divergence.
  (#81 on the list of 100 mathematical theorems)
*)

section \<open>The Prime Harmonic Series\<close>
theory Prime_Harmonic
imports
  "HOL-Analysis.Analysis"
  "HOL-Number_Theory.Number_Theory"
  Prime_Harmonic_Misc
  Squarefree_Nat
begin

subsection \<open>Auxiliary equalities and inequalities\<close>

text \<open>
  First of all, we prove the following result about rearranging a product over a set into a sum
  over all subsets of that set.
\<close>
lemma prime_harmonic_aux1:
  fixes A :: "'a :: field set"
  shows "finite A \<Longrightarrow> (\<Prod>x\<in>A. 1 + 1 / x) = (\<Sum>x\<in>Pow A. 1 / \<Prod>x)"
  by sorry

text \<open>
  Next, we prove a simple and reasonably accurate upper bound for the sum of the squares of any
  subset of the natural numbers, derived by simple telescoping. Our upper bound is approximately
  1.67; the exact value is $\frac{\pi^2}{6} \approx 1.64$. (cf. Basel problem)
\<close>
lemma prime_harmonic_aux2:
  assumes "finite (A :: nat set)"
  shows   "(\<Sum>k\<in>A. 1 / (real k ^ 2)) \<le> 5/3"
  by sorry


subsection \<open>Estimating the partial sums of the Prime Harmonic Series\<close>

text \<open>
  We are now ready to show our main result: the value of the partial prime harmonic sum over
  all primes no greater than $n$ is bounded from below by the $n$-th harmonic number
  $H_n$ minus some constant.

  In our case, this constant will be $\frac{5}{3}$. As mentioned before, using a
  proof of the Basel problem can improve this to $\frac{\pi^2}{6}$, but the improvement is very
  small and the proof of the Basel problem is a very complex one.

  The exact asymptotic behaviour of the partial sums is actually $\ln (\ln n) + M$, where $M$
  is the Meissel--Mertens constant (approximately 0.261).
\<close>
theorem prime_harmonic_lower:
  assumes n: "n \<ge> 2"
  shows "(\<Sum>p\<leftarrow>primes_upto n. 1 / real p) \<ge> ln (harm n) - ln (5/3)"
  by sorry

text \<open>
  We can use the inequality $\ln (n + 1) \le H_n$ to estimate the asymptotic growth of the partial
  prime harmonic series. Note that $H_n \sim \ln n + \gamma$ where $\gamma$ is the
  Euler--Mascheroni constant (approximately 0.577), so we lose some accuracy here.
\<close>
corollary prime_harmonic_lower':
  assumes n: "n \<ge> 2"
  shows "(\<Sum>p\<leftarrow>primes_upto n. 1 / real p) \<ge> ln (ln (n + 1)) - ln (5/3)"
  by sorry


(* TODO: Not needed in Isabelle 2016 *)
lemma Bseq_eventually_mono:
  assumes "eventually (\<lambda>n. norm (f n) \<le> norm (g n)) sequentially" "Bseq g"
  shows   "Bseq f"
  by sorry

lemma Bseq_add:
  assumes "Bseq (f :: nat \<Rightarrow> 'a :: real_normed_vector)"
  shows   "Bseq (\<lambda>x. f x + c)"
  by sorry

lemma convergent_imp_Bseq: "convergent f \<Longrightarrow> Bseq f"
  by sorry

(* END TODO *)

text \<open>
  We now use our last estimate to show that the prime harmonic series diverges. This is obvious,
  since it is bounded from below by $\ln (\ln (n + 1))$ minus some constant, which obviously
  tends to infinite.

  Directly using the divergence of the harmonic series would also be possible and shorten this
  proof a bit..
\<close>
corollary prime_harmonic_series_unbounded:
  "\<not>Bseq (\<lambda>n. \<Sum>p\<leftarrow>primes_upto n. 1 / p)" (is "\<not>Bseq ?f")
  by sorry

corollary prime_harmonic_series_diverges:
  "\<not>convergent (\<lambda>n. \<Sum>p\<leftarrow>primes_upto n. 1 / p)"
  by sorry

end
