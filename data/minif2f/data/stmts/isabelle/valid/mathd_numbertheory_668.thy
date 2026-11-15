(*
  Authors: Wenda Li
*)

theory mathd_numbertheory_668 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
    "HOL-Number_Theory.Number_Theory"
begin

theorem mathd_numbertheory_668:
  fixes l r::int
  assumes "0\<le>l" "l<7" "0\<le>r" "r<7"
    and "(l * (2 + 3)) mod 7 = 1"
    and "\<exists>x y::int. 0 \<le> x \<and> x < 7 \<and>
      0 \<le> y \<and> y < 7 \<and>
      (x * 2) mod 7 = 1 \<and> (y * 3) mod 7 = 1 \<and>
      r = (x + y) mod 7"
  shows "l - r = 1"
  by sorry

end
