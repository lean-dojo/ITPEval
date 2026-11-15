section \<open>The Weighted Arithmetic--Geometric Mean Inequality\<close>
theory Weighted_Arithmetic_Geometric_Mean
  imports Complex_Main
begin

subsection \<open>Auxiliary Facts\<close>

lemma root_powr_inverse': "0 < n \<Longrightarrow> 0 \<le> x \<Longrightarrow> root n x = x powr (1/n)"
  by sorry

lemma powr_sum_distrib_real_right:
  assumes "a \<noteq> 0"
  shows   "(\<Prod>x\<in>X. a powr e x :: real) = a powr (\<Sum>x\<in>X. e x)"
  by sorry

lemma powr_sum_distrib_real_left:
  assumes "\<And>x. x \<in> X \<Longrightarrow> a x \<ge> 0"
  shows   "(\<Prod>x\<in>X. a x powr e :: real) = (\<Prod>x\<in>X. a x) powr e"
  by sorry

lemma prod_ge_pointwise_le_imp_pointwise_eq:
  fixes f :: "'a \<Rightarrow> real"
  assumes "finite X"
  assumes ge: "prod f X \<ge> prod g X"
  assumes nonneg: "\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0"
  assumes pos: "\<And>x. x \<in> X \<Longrightarrow> g x > 0"
  assumes le: "\<And>x. x \<in> X \<Longrightarrow> f x \<le> g x" and x: "x \<in> X"
  shows   "f x = g x"
  by sorry

lemma powr_right_real_eq_iff:
  assumes "a \<ge> (0 :: real)"
  shows   "a powr x = a powr y \<longleftrightarrow> a = 0 \<or> a = 1 \<or> x = y"
  by sorry

lemma powr_left_real_eq_iff:
  assumes "a \<ge> (0 :: real)" "b \<ge> 0" "x \<noteq> 0"
  shows   "a powr x = b powr x \<longleftrightarrow> a = b"
  by sorry

lemma exp_real_eq_one_plus_iff:
  fixes x :: real
  shows "exp x = 1 + x \<longleftrightarrow> x = 0"
  by sorry


subsection \<open>The Inequality\<close>

text \<open>
  We first prove the equality under the assumption that all the $a_i$ and $w_i$ are positive.
\<close>
lemma weighted_arithmetic_geometric_mean_pos:
  fixes a w :: "'a \<Rightarrow> real"
  assumes "finite X"
  assumes pos1: "\<And>x. x \<in> X \<Longrightarrow> a x > 0"
  assumes pos2: "\<And>x. x \<in> X \<Longrightarrow> w x > 0"
  assumes sum_weights: "(\<Sum>x\<in>X. w x) = 1"
  shows   "(\<Prod>x\<in>X. a x powr w x) \<le> (\<Sum>x\<in>X. w x * a x)"
  by sorry

text \<open>
  We can now relax the positivity assumptions to non-negativity: if one of the $a_i$ is
  zero, the theorem becomes trivial (note that $0^0 = 0$ by convention for the real-valued
  power operator \<^term>\<open>(powr) :: real \<Rightarrow> real \<Rightarrow> real\<close>).

  Otherwise, we can simply remove all the indices that have weight 0 and apply the
  above auxiliary version of the theorem.
\<close>
theorem weighted_arithmetic_geometric_mean:
  fixes a w :: "'a \<Rightarrow> real"
  assumes "finite X"
  assumes nonneg1: "\<And>x. x \<in> X \<Longrightarrow> a x \<ge> 0"
  assumes nonneg2: "\<And>x. x \<in> X \<Longrightarrow> w x \<ge> 0"
  assumes sum_weights: "(\<Sum>x\<in>X. w x) = 1"
  shows   "(\<Prod>x\<in>X. a x powr w x) \<le> (\<Sum>x\<in>X. w x * a x)"
  by sorry

text \<open>
  We can derive the regular arithmetic/geometric mean inequality from this by simply
  setting all the weights to $\frac{1}{n}$:
\<close>
corollary arithmetic_geometric_mean:
  fixes a :: "'a \<Rightarrow> real"
  assumes "finite X"
  defines "n \<equiv> card X"
  assumes nonneg: "\<And>x. x \<in> X \<Longrightarrow> a x \<ge> 0"
  shows   "root n (\<Prod>x\<in>X. a x) \<le> (\<Sum>x\<in>X. a x) / n"
  by sorry


subsection \<open>The Equality Case\<close>

text \<open>
  Next, we show that weighted arithmetic and geometric mean are equal if and only if all the 
  $a_i$ are equal.

  We first prove the more difficult direction as a lemmas and again first assume positivity
  of all $a_i$ and $w_i$ and will relax this somewhat later.
\<close>
lemma weighted_arithmetic_geometric_mean_eq_iff_pos:
  fixes a w :: "'a \<Rightarrow> real"
  assumes "finite X"
  assumes pos1: "\<And>x. x \<in> X \<Longrightarrow> a x > 0"
  assumes pos2: "\<And>x. x \<in> X \<Longrightarrow> w x > 0"
  assumes sum_weights: "(\<Sum>x\<in>X. w x) = 1"
  assumes eq: "(\<Prod>x\<in>X. a x powr w x) = (\<Sum>x\<in>X. w x * a x)"
  shows   "\<forall>x\<in>X. \<forall>y\<in>X. a x = a y"
  by sorry

text \<open>
  We can now show the full theorem and relax the positivity condition on the $a_i$ to
  non-negativity. This is possible because if some $a_i$ is zero and the two means
  coincide, then the product is obviously 0, but the sum can only be 0 if \<^term>\<open>all\<close>
  the $a_i$ are 0.
\<close>
theorem weighted_arithmetic_geometric_mean_eq_iff:
  fixes a w :: "'a \<Rightarrow> real"
  assumes "finite X"
  assumes nonneg1: "\<And>x. x \<in> X \<Longrightarrow> a x \<ge> 0"
  assumes pos2:    "\<And>x. x \<in> X \<Longrightarrow> w x > 0"
  assumes sum_weights: "(\<Sum>x\<in>X. w x) = 1"
  shows   "(\<Prod>x\<in>X. a x powr w x) = (\<Sum>x\<in>X. w x * a x) \<longleftrightarrow> X \<noteq> {} \<and> (\<forall>x\<in>X. \<forall>y\<in>X. a x = a y)"
  by sorry

text \<open>
  Again, we derive a version for the unweighted arithmetic/geometric mean.
\<close>
corollary arithmetic_geometric_mean_eq_iff:
  fixes a :: "'a \<Rightarrow> real"
  assumes "finite X"
  defines "n \<equiv> card X"
  assumes nonneg: "\<And>x. x \<in> X \<Longrightarrow> a x \<ge> 0"
  shows   "root n (\<Prod>x\<in>X. a x) = (\<Sum>x\<in>X. a x) / n \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X. a x = a y)"
  by sorry


subsection \<open>The Binary Version\<close>

text \<open>
  For convenience, we also derive versions for only two numbers:
\<close>
corollary weighted_arithmetic_geometric_mean_binary:
  fixes w1 w2 x1 x2 :: real
  assumes "x1 \<ge> 0" "x2 \<ge> 0" "w1 \<ge> 0" "w2 \<ge> 0" "w1 + w2 = 1"
  shows   "x1 powr w1 * x2 powr w2 \<le> w1 * x1 + w2 * x2"
  by sorry

corollary weighted_arithmetic_geometric_mean_eq_iff_binary:
  fixes w1 w2 x1 x2 :: real
  assumes "x1 \<ge> 0" "x2 \<ge> 0" "w1 > 0" "w2 > 0" "w1 + w2 = 1"
  shows   "x1 powr w1 * x2 powr w2 = w1 * x1 + w2 * x2 \<longleftrightarrow> x1 = x2"
  by sorry

corollary arithmetic_geometric_mean_binary:
  fixes x1 x2 :: real
  assumes "x1 \<ge> 0" "x2 \<ge> 0"
  shows   "sqrt (x1 * x2) \<le> (x1 + x2) / 2"
  by sorry

corollary arithmetic_geometric_mean_eq_iff_binary:
  fixes x1 x2 :: real
  assumes "x1 \<ge> 0" "x2 \<ge> 0"
  shows   "sqrt (x1 * x2) = (x1 + x2) / 2 \<longleftrightarrow> x1 = x2"
  by sorry

end