(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_35 imports
  Complex_Main
begin

theorem mathd_algebra_35:
  fixes p q :: "real \<Rightarrow> real"
  assumes h0 : "\<And>x. p x = 2 - x^2"
    and h1 : "\<And>x. (x\<noteq>0) \<Longrightarrow> q x = 6 / x"
  shows "p (q 2) = -7"
  by sorry

end