(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_245 imports
  Complex_Main
begin

theorem mathd_algebra_245:
  fixes x :: real
  assumes h0 : "x \<noteq> 0"
  shows "1/(4/x) * ((3*x^3)/x)^2 * (1/(1 / (2 * x)))^3 = 18 * x^8"
  by sorry
end