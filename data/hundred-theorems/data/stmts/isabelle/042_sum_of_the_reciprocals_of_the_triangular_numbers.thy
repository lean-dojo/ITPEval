(*
  Title:     HOL/ex/Triangular_Numbers.thy
  Author:    Manuel Eberl, TU München
*)
section \<open>Triangular Numbers\<close>
theory Triangular_Numbers
  imports Complex_Main
begin

definition triangle_num :: "nat \<Rightarrow> nat" where
  "triangle_num n = (n * (n + 1)) div 2"

lemma real_triangle_num:
  "real (triangle_num n) = real n * (real n + 1) / 2"
  by sorry

lemma triangle_num_altdef: "triangle_num n = (\<Sum>k\<le>n. k)"
  by sorry


lemma triangle_num_ge: "triangle_num n \<ge> n"
  by sorry

lemma triangle_num_Suc: "triangle_num (Suc n) = triangle_num n + Suc n"
  by sorry

lemma triangle_num_0 [simp]: "triangle_num 0 = 0"
  and triangle_num_1 [simp]: "triangle_num 1 = 1"
  by sorry

lemma triangle_num_numeral [simp]:
  "triangle_num (numeral n) = fst (divmod (n * Num.inc n) (Num.Bit0 Num.One))"
  by sorry

lemma triangle_num_eq_0_iff [simp]: "triangle_num n = 0 \<longleftrightarrow> n = 0"
  by sorry

lemma triangle_num_gt_0_iff [simp]: "triangle_num n > 0 \<longleftrightarrow> n > 0"
  by sorry


lemma strict_mono_triangle_num: "strict_mono triangle_num"
  by sorry

lemma triangle_num_le: "m \<le> n \<Longrightarrow> triangle_num m \<le> triangle_num n"
  by sorry

lemma triangle_num_less: "m < n \<Longrightarrow> triangle_num m < triangle_num n"
  by sorry

lemma triangle_num_less_iff: "triangle_num m < triangle_num n \<longleftrightarrow> m < n"
  by sorry

lemma triangle_num_le_iff: "triangle_num m \<le> triangle_num n \<longleftrightarrow> m \<le> n"
  by sorry

lemma triangle_num_eq_iff: "triangle_num m = triangle_num n \<longleftrightarrow> m = n"
  by sorry


theorem inverse_triangle_num_sums: "(\<lambda>n. 1 / triangle_num (Suc n)) sums 2"
  by sorry

end