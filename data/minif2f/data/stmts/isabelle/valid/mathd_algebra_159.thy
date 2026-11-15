(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_159 imports
Complex_Main

begin

theorem mathd_algebra_159:
  fixes b :: real
    and f :: "real \<Rightarrow> real"
  assumes h0 : "\<And>x. f x = 3 * x^4 - 7 * x^3 + 2*x^2 - b*x +1"
    and h1 : "f 1 = 1"
  shows "b = -2"
  by sorry


end