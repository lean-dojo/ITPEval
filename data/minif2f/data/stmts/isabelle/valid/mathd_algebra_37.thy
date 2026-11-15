(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_37 imports
  Complex_Main
begin

theorem mathd_algebra_37:
  fixes x y :: real
  assumes h0 : "x+y=7"
    and h1 : "3 * x + y = 45"
  shows "x^2 - y^2 = 217"
  by sorry

end