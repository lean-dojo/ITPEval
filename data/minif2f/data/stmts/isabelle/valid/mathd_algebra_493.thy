(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_493 imports
  Complex_Main
begin

theorem mathd_algebra_493:
  fixes f :: "real \<Rightarrow> real"
  assumes h0 : "\<And>x. f x = x^2 - 4 * (sqrt x) + 1"
  shows "f (f 4) = 70"
  by sorry

end