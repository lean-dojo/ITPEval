(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_126 imports
  Complex_Main
begin

theorem mathd_algebra_126:
  fixes x y :: real
  assumes h0 : "2 * 3 = x - 9"
    and h1 : "2 * (-5) = y + 1"
  shows "x=15 \<and> y = -11"
  by sorry

end