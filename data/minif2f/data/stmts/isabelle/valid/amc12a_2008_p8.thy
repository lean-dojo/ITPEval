(*
  Authors: Albert Qiaochu Jiang
*)

theory amc12a_2008_p8 imports
Complex_Main
begin
theorem amc12a_2008_p8:
  fixes x y::real
  assumes h0: "0 < x \<and> 0 < y"
    and h1: "y^3 = 1"
    and h2: "6 * x^2 = 2 * (6 * y^2)"
  shows "x^3 = 2 * sqrt 2"
  by sorry

end