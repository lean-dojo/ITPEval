(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_132 imports
  Complex_Main
begin

theorem mathd_algebra_132:
  fixes x :: real
    and f g :: "real \<Rightarrow> real"
  assumes h0 : "\<And>x. f x = x + 2"
    and h1 : "\<And>x. g x = x^2"
    and h2 : "f (g x) = g (f x)"
  shows "x = -1/2"
  by sorry

end