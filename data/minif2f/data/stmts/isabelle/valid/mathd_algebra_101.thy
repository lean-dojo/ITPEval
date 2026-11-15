(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_101 imports
  Complex_Main
begin

theorem mathd_algebra_101:
  fixes x :: real
  assumes h0 : "x^2 - 5 * x - 4 \<le> 10"
  shows "x\<ge> -2 \<and> x \<le> 7"
  by sorry

end