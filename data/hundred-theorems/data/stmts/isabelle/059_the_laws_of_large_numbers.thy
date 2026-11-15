(*
   File:     Laws_of_Large_Numbers.thy
   Author:   Manuel Eberl, TU München
*)
section \<open>The Laws of Large Numbers\<close>
theory Laws_of_Large_Numbers
  imports Ergodic_Theory.Shift_Operator
begin

text \<open>
  We prove the strong law of large numbers in the following form: Let $(X_i)_{i\in\mathbb{N}}$
  be a sequence of i.i.d. random variables over a probability space \<open>M\<close>. Further assume that
  the expected value $E[X_0]$ of $X_0$ exists. Then the sequence of random variables
  \[\overline{X}_n = \frac{1}{n} \sum_{i=0}^n X_i\]
  of running averages almost surely converges to $E[X_0]$.
  This means that
  \[\mathcal{P}[\overline{X}_n \longrightarrow E[X_0]] = 1\ .\]

  We start with the strong law.
\<close>


subsection \<open>The strong law\<close>

text \<open>
  The proof uses Birkhoff's Theorem from Gouëzel's formalisation of ergodic theory~\<^cite>\<open>"gouezel"\<close>
  and the fact that the shift operator $T(x_1, x_2, x_3, \ldots) = (x_2, x_3, \ldots)$ is ergodic.
  This proof can be found in various textbooks on probability theory/ergodic
  theory, e.g. the ones by Krengel~\<^cite>\<open>\<open>p.~24\<close> in "krengel"\<close> and
  Simmonet~\<^cite>\<open>\<open>Chapter 15, pp.~311--325\<close> in "Simonnet1996"\<close>.
\<close>
theorem (in prob_space) strong_law_of_large_numbers_iid:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes indep: "indep_vars (\<lambda>_. borel) X UNIV"
  assumes distr: "\<And>i. distr M borel (X i) = distr M borel (X 0)"
  assumes L1:    "integrable M (X 0)"
  shows "AE x in M. (\<lambda>n. (\<Sum>i<n. X i x) / n) \<longlonglongrightarrow> expectation (X 0)"
  by sorry


subsection \<open>The weak law\<close>

text \<open>
  To go from the strong law to the weak one, we need the fact that almost sure convergence
  implies convergence in probability. We prove this for sequences of random variables here.
\<close>
lemma (in prob_space) AE_convergence_imp_convergence_in_prob:
  assumes [measurable]: "\<And>i. random_variable borel (X i)" "random_variable borel Y"
  assumes AE: "AE x in M. (\<lambda>i. X i x) \<longlonglongrightarrow> Y x"
  assumes "\<epsilon> > (0 :: real)"
  shows   "(\<lambda>i. prob {x\<in>space M. \<bar>X i x - Y x\<bar> > \<epsilon>}) \<longlonglongrightarrow> 0"
  by sorry

text \<open>
  The weak law is now a simple corollary: we again have the same setting as before. The weak
  law now states that $\overline{X}_n$ converges to $E[X_0]$ in probability. This means that
  for any \<open>\<epsilon> > 0\<close>, the probability that $|\overline{X}_n - X_0| > \varepsilon$ vanishes as
  \<open>n \<rightarrow> \<infinity>\<close>.
\<close>
corollary (in prob_space) weak_law_of_large_numbers_iid:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and \<epsilon> :: real
  assumes indep: "indep_vars (\<lambda>_. borel) X UNIV"
  assumes distr: "\<And>i. distr M borel (X i) = distr M borel (X 0)"
  assumes L1:    "integrable M (X 0)"
  assumes "\<epsilon> > 0"
  shows   "(\<lambda>n. prob {x\<in>space M. \<bar>(\<Sum>i<n. X i x) / n - expectation (X 0)\<bar> > \<epsilon>}) \<longlonglongrightarrow> 0"
  by sorry

end