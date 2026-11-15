(*
   File:     HOL/Analysis/Ball_Volume.thy
   Author:   Manuel Eberl, TU München
*)

section \<open>The Volume of an \<open>n\<close>-Dimensional Ball\<close>

theory Ball_Volume
  imports Gamma_Function Lebesgue_Integral_Substitution
begin

text \<open>
  We define the volume of the unit ball in terms of the Gamma function. Note that the
  dimension need not be an integer; we also allow fractional dimensions, although we do
  not use this case or prove anything about it for now.
\<close>
definition\<^marker>\<open>tag important\<close> unit_ball_vol :: "real \<Rightarrow> real" where
  "unit_ball_vol n = pi powr (n / 2) / Gamma (n / 2 + 1)"

lemma unit_ball_vol_pos [simp]: "n \<ge> 0 \<Longrightarrow> unit_ball_vol n > 0"
  by sorry

lemma unit_ball_vol_nonneg [simp]: "n \<ge> 0 \<Longrightarrow> unit_ball_vol n \<ge> 0"
  by sorry

text \<open>
  We first need the value of the following integral, which is at the core of
  computing the measure of an \<open>n + 1\<close>-dimensional ball in terms of the measure of an
  \<open>n\<close>-dimensional one.
\<close>
lemma emeasure_cball_aux_integral:
  "(\<integral>\<^sup>+x. indicator {-1..1} x * sqrt (1 - x\<^sup>2) ^ n \<partial>lborel) =
      ennreal (Beta (1 / 2) (real n / 2 + 1))"
  by sorry

lemma real_sqrt_le_iff': "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> sqrt x \<le> y \<longleftrightarrow> x \<le> y ^ 2"
  by sorry

text \<open>
  Isabelle's type system makes it very difficult to do an induction over the dimension
  of a Euclidean space type, because the type would change in the inductive step. To avoid
  this problem, we instead formulate the problem in a more concrete way by unfolding the
  definition of the Euclidean norm.
\<close>
lemma emeasure_cball_aux:
  assumes "finite A" "r > 0"
  shows   "emeasure (Pi\<^sub>M A (\<lambda>_. lborel))
             ({f. sqrt (\<Sum>i\<in>A. (f i)\<^sup>2) \<le> r} \<inter> space (Pi\<^sub>M A (\<lambda>_. lborel))) =
             ennreal (unit_ball_vol (real (card A)) * r ^ card A)"
  by sorry


text \<open>
  We now get the main theorem very easily by just applying the above lemma.
\<close>
context
  fixes c :: "'a :: euclidean_space" and r :: real
  assumes r: "r \<ge> 0"
begin

theorem\<^marker>\<open>tag unimportant\<close> emeasure_cball:
  "emeasure lborel (cball c r) = ennreal (unit_ball_vol (DIM('a)) * r ^ DIM('a))"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> content_cball:
  "content (cball c r) = unit_ball_vol (DIM('a)) * r ^ DIM('a)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> emeasure_ball:
  "emeasure lborel (ball c r) = ennreal (unit_ball_vol (DIM('a)) * r ^ DIM('a))"
  by sorry

corollary\<^marker>\<open>tag important\<close> content_ball:
  "content (ball c r) = unit_ball_vol (DIM('a)) * r ^ DIM('a)"
  by sorry

end


text \<open>
  Lastly, we now prove some nicer explicit formulas for the volume of the unit balls in
  the cases of even and odd integer dimensions.
\<close>
lemma unit_ball_vol_even:
  "unit_ball_vol (real (2 * n)) = pi ^ n / fact n"
  by sorry

lemma unit_ball_vol_odd':
        "unit_ball_vol (real (2 * n + 1)) = pi ^ n / pochhammer (1 / 2) (Suc n)"
  and unit_ball_vol_odd:
        "unit_ball_vol (real (2 * n + 1)) =
           (2 ^ (2 * Suc n) * fact (Suc n)) / fact (2 * Suc n) * pi ^ n"
  by sorry

lemma unit_ball_vol_numeral:
  "unit_ball_vol (numeral (Num.Bit0 n)) = pi ^ numeral n / fact (numeral n)" (is ?th1)
  "unit_ball_vol (numeral (Num.Bit1 n)) = 2 ^ (2 * Suc (numeral n)) * fact (Suc (numeral n)) /
    fact (2 * Suc (numeral n)) * pi ^ numeral n" (is ?th2)
  by sorry

lemmas eval_unit_ball_vol = unit_ball_vol_numeral fact_numeral


text \<open>
  Just for fun, we compute the volume of unit balls for a few dimensions.
\<close>
lemma unit_ball_vol_0 [simp]: "unit_ball_vol 0 = 1"
  by sorry

lemma unit_ball_vol_1 [simp]: "unit_ball_vol 1 = 2"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close>
          unit_ball_vol_2: "unit_ball_vol 2 = pi"
      and unit_ball_vol_3: "unit_ball_vol 3 = 4 / 3 * pi"
      and unit_ball_vol_4: "unit_ball_vol 4 = pi\<^sup>2 / 2"
      and unit_ball_vol_5: "unit_ball_vol 5 = 8 / 15 * pi\<^sup>2"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> circle_area:
  "r \<ge> 0 \<Longrightarrow> content (ball c r :: (real ^ 2) set) = r ^ 2 * pi"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> sphere_volume:
  "r \<ge> 0 \<Longrightarrow> content (ball c r :: (real ^ 3) set) = 4 / 3 * r ^ 3 * pi"
  by sorry

text \<open>
  Useful equivalent forms
\<close>
corollary\<^marker>\<open>tag unimportant\<close> content_ball_eq_0_iff [simp]: "content (ball c r) = 0 \<longleftrightarrow> r \<le> 0"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> content_ball_gt_0_iff [simp]: "0 < content (ball z r) \<longleftrightarrow> 0 < r"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> content_cball_eq_0_iff [simp]: "content (cball c r) = 0 \<longleftrightarrow> r \<le> 0"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> content_cball_gt_0_iff [simp]: "0 < content (cball z r) \<longleftrightarrow> 0 < r"
  by sorry

end
