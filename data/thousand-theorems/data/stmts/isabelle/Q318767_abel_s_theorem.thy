(*
  Statement-only formalization of thousand-theorems corpus artifact Q318767,
  "Abel's theorem": a convergent real or complex coefficient series determines
  the boundary limit of its power series, from the left in the real case and
  within every positive Stolz cone in the complex case. This file contains no
  proof.
*)

theory Q318767_abel_s_theorem
  imports Complex_Main
begin

definition stolz_cone :: "real \<Rightarrow> complex set" where
  "stolz_cone s = {z. \<bar>Im z\<bar> < s * (1 - Re z)}"

theorem abel_stolz_cone:
  fixes f :: "nat \<Rightarrow> complex"
    and l :: complex
    and s :: real
  assumes "(\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> l"
    and "0 < s"
  shows "((\<lambda>z. suminf (\<lambda>n. f n * z ^ n)) \<longlongrightarrow> l)
    (at 1 within stolz_cone s)"
  sorry

theorem abel_real_left:
  fixes f :: "nat \<Rightarrow> real"
    and l :: real
  assumes "(\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> l"
  shows "((\<lambda>x. suminf (\<lambda>n. f n * x ^ n)) \<longlongrightarrow> l)
    (at_left 1)"
  sorry

end
