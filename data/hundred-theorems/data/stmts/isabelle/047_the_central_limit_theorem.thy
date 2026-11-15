(*  Title:     HOL/Probability/Central_Limit_Theorem.thy
    Authors:   Jeremy Avigad (CMU), Luke Serafin (CMU)
*)

section \<open>The Central Limit Theorem\<close>

theory Central_Limit_Theorem
  imports Levy
begin

theorem (in prob_space) central_limit_theorem_zero_mean:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and \<mu> :: "real measure"
    and \<sigma> :: real
    and S :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes X_indep: "indep_vars (\<lambda>i. borel) X UNIV"
    and X_mean_0: "\<And>n. expectation (X n) = 0"
    and \<sigma>_pos: "\<sigma> > 0"
    and X_square_integrable: "\<And>n. integrable M (\<lambda>x. (X n x)\<^sup>2)"
    and X_variance: "\<And>n. variance (X n) = \<sigma>\<^sup>2"
    and X_distrib: "\<And>n. distr M borel (X n) = \<mu>"
  defines "S n \<equiv> \<lambda>x. \<Sum>i<n. X i x"
  shows "weak_conv_m (\<lambda>n. distr M borel (\<lambda>x. S n x / sqrt (n * \<sigma>\<^sup>2))) std_normal_distribution"
  by sorry

theorem (in prob_space) central_limit_theorem:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and \<mu> :: "real measure"
    and \<sigma> :: real
    and S :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes X_indep: "indep_vars (\<lambda>i. borel) X UNIV"
    and X_mean: "\<And>n. expectation (X n) = m"
    and \<sigma>_pos: "\<sigma> > 0"
    and X_square_integrable: "\<And>n. integrable M (\<lambda>x. (X n x)\<^sup>2)"
    and X_variance: "\<And>n. variance (X n) = \<sigma>\<^sup>2"
    and X_distrib: "\<And>n. distr M borel (X n) = \<mu>"
  defines "X' i x \<equiv> X i x - m"
  shows "weak_conv_m (\<lambda>n. distr M borel (\<lambda>x. (\<Sum>i<n. X' i x) / sqrt (n*\<sigma>\<^sup>2))) std_normal_distribution"
  by sorry

end
