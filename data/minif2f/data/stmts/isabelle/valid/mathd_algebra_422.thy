(*
  Authors: Wenda Li
*)

theory mathd_algebra_422 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
  
begin

theorem mathd_algebra_422:
  fixes x :: real and \<sigma>::"real \<Rightarrow> real"
  assumes "bij \<sigma>"
    and \<sigma>:"\<forall> x. \<sigma> x = 5 * x - 12"
    and "\<sigma> (x + 1) = (inv \<sigma>) x" 
  shows "x = 47 / 24"
  by sorry

end   