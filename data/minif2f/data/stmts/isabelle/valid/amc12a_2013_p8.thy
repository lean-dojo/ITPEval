(*
  Authors: Albert Qiaochu Jiang
*)

theory amc12a_2013_p8 imports
  Complex_Main
begin

theorem amc12a_2013_p8:
  fixes x y :: real
  assumes h0 : "x\<noteq>0"
    and h1 : "y\<noteq>0"
    and h2 : "x\<noteq>y"
    and h3 : "x + 2/x = y + 2/y"
  shows "x * y = 2"
  by sorry

end