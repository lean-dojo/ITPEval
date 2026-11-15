(*
  Authors: Albert Qiaochu Jiang
*)

theory amc12a_2009_p5 imports
  Complex_Main
begin

theorem amc12a_2009_p5:
  fixes x :: real
  assumes h0 : "x^3 - (x+1) * (x-1) * x = 5"
  shows "x^3 = 125"
  by sorry


end