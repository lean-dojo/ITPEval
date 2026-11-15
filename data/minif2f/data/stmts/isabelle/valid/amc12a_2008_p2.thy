(*
  Authors: Albert Qiaochu Jiang
*)

theory amc12a_2008_p2 imports
  Complex_Main
begin

theorem amc12a_2008_p2:
  fixes x :: real
  assumes h0 : "x * (1 / 2 + 2 / 3) = 1"
  shows "x = 6/7"
  by sorry

end