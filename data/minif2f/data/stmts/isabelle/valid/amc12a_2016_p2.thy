(*
  Authors: Albert Qiaochu Jiang
*)

theory amc12a_2016_p2 imports
Complex_Main

begin

theorem amc12a_2016_p2:
  fixes x :: real
  assumes h0 : "10 powr x * 100 powr (2*x) = (1000::real)^5"
  shows "x=3"
  by sorry


end
