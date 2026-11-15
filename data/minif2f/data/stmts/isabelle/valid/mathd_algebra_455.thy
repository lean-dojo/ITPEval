(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_455 imports
  Complex_Main
begin

theorem mathd_algebra_455:
  fixes x :: real
  assumes h0 : "2 * (2 * (2 * (2 * x))) = 48"
  shows "x=3"
  by sorry

end