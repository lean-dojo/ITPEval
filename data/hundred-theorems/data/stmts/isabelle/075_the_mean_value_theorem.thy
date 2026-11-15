(*
  Statement-only formalization of the mean value theorem from Hundred
  Theorems item 075. This file contains no proof.
*)

theory Mean_Value_Theorem
  imports Complex_Main
begin

theorem hundred_theorems_mean_value:
  fixes f :: "real \<Rightarrow> real"
    and a b :: real
  assumes "a < b"
    and "continuous_on {a..b} f"
    and "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> f differentiable (at x)"
  shows "\<exists>l z.
    a < z \<and> z < b \<and> DERIV f z :> l
      \<and> f b - f a = (b - a) * l"
  sorry

end
