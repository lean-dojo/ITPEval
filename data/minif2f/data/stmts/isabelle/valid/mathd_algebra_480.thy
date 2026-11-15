(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_480 imports
  Complex_Main
begin

theorem mathd_algebra_480:
  fixes f :: "real \<Rightarrow> real"
  assumes h0 : "\<And>x. x<0 \<Longrightarrow> f x = -(x^2)-1"
    and h1 : "\<And>x. (0 \<le> x \<and> x < 4) \<Longrightarrow> f x = 2"
    and h2 : "\<And>x. x\<ge>4 \<Longrightarrow> f x = sqrt x"
  shows "f pi = 2"
  by sorry
end