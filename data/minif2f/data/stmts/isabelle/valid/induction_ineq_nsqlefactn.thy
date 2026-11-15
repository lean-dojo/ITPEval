(*
  Authors: Wenda Li
*)

theory induction_ineq_nsqlefactn
 imports
  Complex_Main
begin

theorem induction_ineq_nsqlefactn:
  fixes n::nat
  assumes " 4 \<le> n"
  shows  "n^2 \<le> fact n" using assms
  by sorry

end
