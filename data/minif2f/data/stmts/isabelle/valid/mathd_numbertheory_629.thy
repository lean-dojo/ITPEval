(*
  Authors: Wenda Li
*)

theory mathd_numbertheory_629 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
begin

theorem mathd_numbertheory_629 :
  "(LEAST t::nat. 0 < t \<and> (lcm 12 t)^3 = (12 * t)^2) = 18"
  by sorry

end
