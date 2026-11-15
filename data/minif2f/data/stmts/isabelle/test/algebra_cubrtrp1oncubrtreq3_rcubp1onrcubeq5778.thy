(*
  Authors: Wenda Li
*)

theory algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Number_Theory.Number_Theory"
begin

theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778:
  fixes r :: real
  assumes "\<exists>x :: real. x^3 = r \<and> x + 1 / x = 3"
  shows "r^3 + 1 / r^3 = 5778"
  by sorry

end
