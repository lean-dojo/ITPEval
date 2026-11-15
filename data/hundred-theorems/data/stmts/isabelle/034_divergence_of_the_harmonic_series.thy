(*  Title:    HOL/Analysis/Harmonic_Numbers.thy
    Author:   Manuel Eberl, TU München
*)

section \<open>Harmonic Numbers\<close>

theory Harmonic_Numbers
imports
  Complex_Transcendental
  Summation_Tests
begin

text \<open>
  The definition of the Harmonic Numbers and the Euler-Mascheroni constant.
  Also provides a reasonably accurate approximation of \<^term>\<open>ln 2 :: real\<close>
  and the Euler-Mascheroni constant.
\<close>

subsection \<open>The Harmonic numbers\<close>

definition\<^marker>\<open>tag important\<close> harm :: "nat \<Rightarrow> 'a :: real_normed_field" where
  "harm n = (\<Sum>k=1..n. inverse (of_nat k))"

lemma harm_altdef: "harm n = (\<Sum>k<n. inverse (of_nat (Suc k)))"
  by sorry

lemma harm_Suc: "harm (Suc n) = harm n + inverse (of_nat (Suc n))"
  by sorry

lemma harm_nonneg: "harm n \<ge> (0 :: 'a :: {real_normed_field,linordered_field})"
  by sorry

lemma harm_pos: "n > 0 \<Longrightarrow> harm n > (0 :: 'a :: {real_normed_field,linordered_field})"
  by sorry

lemma harm_mono: "m \<le> n \<Longrightarrow> harm m \<le> (harm n :: 'a :: {real_normed_field,linordered_field})"
  by sorry

lemma of_real_harm: "of_real (harm n) = harm n"
  by sorry

lemma abs_harm [simp]: "(abs (harm n) :: real) = harm n"
  by sorry

lemma norm_harm: "norm (harm n) = harm n"
  by sorry

lemma harm_expand:
  "harm 0 = 0"
  "harm (Suc 0) = 1"
  "harm (numeral n) = harm (pred_numeral n) + inverse (numeral n)"
  by sorry

theorem not_convergent_harm: "\<not>convergent (harm :: nat \<Rightarrow> 'a :: real_normed_field)"
  by sorry

lemma harm_pos_iff [simp]: "harm n > (0 :: 'a :: {real_normed_field,linordered_field}) \<longleftrightarrow> n > 0"
  by sorry

lemma ln_diff_le_inverse:
  assumes "x \<ge> (1::real)"
  shows   "ln (x + 1) - ln x < 1 / x"
  by sorry

lemma ln_le_harm: "ln (real n + 1) \<le> (harm n :: real)"
  by sorry

lemma harm_at_top: "filterlim (harm :: nat \<Rightarrow> real) at_top sequentially"
  by sorry


subsection \<open>The Euler-Mascheroni constant\<close>

text \<open>
  The limit of the difference between the partial harmonic sum and the natural logarithm
  (approximately 0.577216). This value occurs e.g. in the definition of the Gamma function.
 \<close>
definition euler_mascheroni :: "'a :: real_normed_algebra_1" where
  "euler_mascheroni = of_real (lim (\<lambda>n. harm n - ln (of_nat n)))"

lemma of_real_euler_mascheroni [simp]: "of_real euler_mascheroni = euler_mascheroni"
  by sorry

lemma harm_ge_ln: "harm n \<ge> ln (real n + 1)"
  by sorry

lemma decseq_harm_diff_ln: "decseq (\<lambda>n. harm (Suc n) - ln (Suc n))"
  by sorry

lemma euler_mascheroni_sequence_nonneg:
  assumes "n > 0"
  shows   "harm n - ln (real n) \<ge> (0 :: real)"
  by sorry

lemma euler_mascheroni_convergent: "convergent (\<lambda>n. harm n - ln n)"
  by sorry

lemma euler_mascheroni_sequence_decreasing:
  "m > 0 \<Longrightarrow> m \<le> n \<Longrightarrow> harm n - ln (of_nat n) \<le> harm m - ln (of_nat m :: real)"
  by sorry
  
lemma\<^marker>\<open>tag important\<close> euler_mascheroni_LIMSEQ:
  "(\<lambda>n. harm n - ln (of_nat n) :: real) \<longlonglongrightarrow> euler_mascheroni"
  by sorry

lemma harm_le: "n \<ge> 1 \<Longrightarrow> harm n \<le> ln n + 1"
  by sorry

lemma euler_mascheroni_LIMSEQ_of_real:
  "(\<lambda>n. of_real (harm n - ln (of_nat n))) \<longlonglongrightarrow>
      (euler_mascheroni :: 'a :: {real_normed_algebra_1, topological_space})"
  by sorry

lemma euler_mascheroni_sum_real:
  "(\<lambda>n. inverse (of_nat (n+1)) + ln (of_nat (n+1)) - ln (of_nat (n+2)) :: real)
       sums euler_mascheroni"
  by sorry

lemma euler_mascheroni_sum:
  "(\<lambda>n. inverse (of_nat (n+1)) + of_real (ln (of_nat (n+1))) - of_real (ln (of_nat (n+2))))
       sums (euler_mascheroni :: 'a :: {banach, real_normed_field})"
  by sorry

theorem alternating_harmonic_series_sums: "(\<lambda>k. (-1)^k / real_of_nat (Suc k)) sums ln 2"
  by sorry

lemma alternating_harmonic_series_sums':
  "(\<lambda>k. inverse (real_of_nat (2*k+1)) - inverse (real_of_nat (2*k+2))) sums ln 2"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Bounds on the Euler-Mascheroni constant\<close>
(* TODO: perhaps move this section away to remove unnecessary dependency on integration *)

(* TODO: Move? *)
lemma ln_inverse_approx_le:
  assumes "(x::real) > 0" "a > 0"
  shows   "ln (x + a) - ln x \<le> a * (inverse x + inverse (x + a))/2" (is "_ \<le> ?A")
  by sorry

lemma ln_inverse_approx_ge:
  assumes "(x::real) > 0" "x < y"
  shows   "ln y - ln x \<ge> 2 * (y - x) / (x + y)" (is "_ \<ge> ?A")
  by sorry

lemma euler_mascheroni_lower:
          "euler_mascheroni \<ge> harm (Suc n) - ln (real_of_nat (n + 2)) + 1/real_of_nat (2 * (n + 2))"
    and euler_mascheroni_upper:
          "euler_mascheroni \<le> harm (Suc n) - ln (real_of_nat (n + 2)) + 1/real_of_nat (2 * (n + 1))"
  by sorry

lemma euler_mascheroni_pos: "euler_mascheroni > (0::real)"
  by sorry

context
begin

private lemma ln_approx_aux:
  fixes n :: nat and x :: real
  defines "y \<equiv> (x-1)/(x+1)"
  assumes x: "x > 0" "x \<noteq> 1"
  shows "inverse (2*y^(2*n+1)) * (ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))) \<in>
            {0..(1 / (1 - y^2) / of_nat (2*n+1))}"
proof -
  from x have norm_y: "norm y < 1" unfolding y_def by simp
  from power_strict_mono[OF this, of 2] have norm_y': "norm y^2 < 1" by simp

  let ?f = "\<lambda>k. 2 * y ^ (2*k+1) / of_nat (2*k+1)"
  note sums = ln_series_quadratic[OF x(1)]
  define c where "c = inverse (2*y^(2*n+1))"
  let ?d = "c * (ln x - (\<Sum>k<n. ?f k))"
  have "\<And>k. y\<^sup>2^k / of_nat (2*(k+n)+1) \<le> y\<^sup>2 ^ k / of_nat (2*n+1)"
    by (intro divide_left_mono mult_right_mono mult_pos_pos zero_le_power[of "y^2"]) simp_all
  moreover {
    have "(\<lambda>k. ?f (k + n)) sums (ln x - (\<Sum>k<n. ?f k))"
      using sums_split_initial_segment[OF sums] by (simp add: y_def)
    hence "(\<lambda>k. c * ?f (k + n)) sums ?d" by (rule sums_mult)
    also have "(\<lambda>k. c * (2*y^(2*(k+n)+1) / of_nat (2*(k+n)+1))) =
                   (\<lambda>k. (c * (2*y^(2*n+1))) * ((y^2)^k / of_nat (2*(k+n)+1)))"
      by (simp only: ring_distribs power_add power_mult) (simp add: mult_ac)
    also from x have "c * (2*y^(2*n+1)) = 1" by (simp add: c_def y_def)
    finally have "(\<lambda>k. (y^2)^k / of_nat (2*(k+n)+1)) sums ?d" by simp
  } note sums' = this
  moreover from norm_y' have "(\<lambda>k. (y^2)^k / of_nat (2*n+1)) sums (1 / (1 - y^2) / of_nat (2*n+1))"
    by (intro sums_divide geometric_sums) (simp_all add: norm_power)
  ultimately have "?d \<le> (1 / (1 - y^2) / of_nat (2*n+1))" by (rule sums_le)
  moreover have "c * (ln x - (\<Sum>k<n. 2 * y ^ (2 * k + 1) / real_of_nat (2 * k + 1))) \<ge> 0"
    by (intro sums_le[OF _ sums_zero sums']) simp_all
  ultimately show ?thesis unfolding c_def by simp
qed

lemma
  fixes n :: nat and x :: real
  defines "y \<equiv> (x-1)/(x+1)"
  defines "approx \<equiv> (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))"
  defines "d \<equiv> y^(2*n+1) / (1 - y^2) / of_nat (2*n+1)"
  assumes x: "x > 1"
  shows   ln_approx_bounds: "ln x \<in> {approx..approx + 2*d}"
  and     ln_approx_abs:    "abs (ln x - (approx + d)) \<le> d"
  by sorry

end

lemma euler_mascheroni_bounds:
  fixes n :: nat assumes "n \<ge> 1" defines "t \<equiv> harm n - ln (of_nat (Suc n)) :: real"
  shows "euler_mascheroni \<in> {t + inverse (of_nat (2*(n+1)))..t + inverse (of_nat (2*n))}"
  by sorry

lemma euler_mascheroni_bounds':
  fixes n :: nat assumes "n \<ge> 1" "ln (real_of_nat (Suc n)) \<in> {l<..<u}"
  shows "euler_mascheroni \<in>
           {harm n - u + inverse (of_nat (2*(n+1)))<..<harm n - l + inverse (of_nat (2*n))}"
  by sorry


text \<open>
  Approximation of \<^term>\<open>ln 2\<close>. The lower bound is accurate to about 0.03; the upper
  bound is accurate to about 0.0015.
\<close>
lemma ln2_ge_two_thirds: "2/3 \<le> ln (2::real)"
  and ln2_le_25_over_36: "ln (2::real) \<le> 25/36"
  by sorry


text \<open>
  Approximation of the Euler-Mascheroni constant. The lower bound is accurate to about 0.0015;
  the upper bound is accurate to about 0.015.
\<close>
lemma euler_mascheroni_gt_19_over_33: "(euler_mascheroni :: real) > 19/33" (is ?th1)
  and euler_mascheroni_less_13_over_22: "(euler_mascheroni :: real) < 13/22" (is ?th2)
  by sorry

end
