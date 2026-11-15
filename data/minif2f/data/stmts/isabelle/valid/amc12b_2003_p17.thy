(*
  Authors: Wenda Li
*)

theory amc12b_2003_p17 imports
  Complex_Main
begin

theorem amc12b_2003_p17:
  fixes x y ::real
  assumes "x>0" "y>0"
    and "ln (x * y^3) =1"
    and "ln (x^2 *  y)  = 1"
  shows "ln (x*y) = 3/5"
  by sorry


end
