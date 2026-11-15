(*
  Authors: Wenda Li
*)

theory mathd_numbertheory_321 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Number_Theory.Number_Theory"
begin

theorem mathd_numbertheory_321:
  fixes n::int
  assumes "0 \<le> n"
    and "n < 1399"
    and "(n * 160) mod 1399 = 1"
  shows "n = 1058"
  by sorry

end
