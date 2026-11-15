(*
  Authors: Wenda Li
*)

theory imo_1978_p5 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
begin

theorem imo_1978_p5:
  fixes n :: nat
    and a :: "nat \<Rightarrow> nat"
  assumes "inj a"
    and "a 0 = 0"
    and "0 < n"
  shows "(\<Sum> k \<in>{1..<n+1}. (1::real) / of_nat k)
    \<le> (\<Sum> k \<in>{1..<n+1}.
      of_nat (a k) / (of_nat k :: real)^2)"
  by sorry

end
