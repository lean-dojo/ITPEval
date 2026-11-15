theory putnam_1970_b4 imports Complex_Main
"HOL-Analysis.Derivative"
begin

theorem putnam_1970_b4:
  fixes x :: "real \<Rightarrow> real"
  assumes hdiff : "\<forall> t \<in> {0::real..1}. x differentiable at t \<and> (deriv x) differentiable at t"
    and hx : "x 1 - x 0 = 1"
    and hv : "deriv x 0 = 0 \<and> deriv x 1 = 0"
    and hs : "\<forall> t \<in> {(0::real)<..<1}. \<bar>deriv x t\<bar> \<le> 3/2"
  shows "\<exists> t \<in> {(0::real)..1}. \<bar>(deriv (deriv x)) t\<bar> \<ge> 9/2"
  sorry

end
