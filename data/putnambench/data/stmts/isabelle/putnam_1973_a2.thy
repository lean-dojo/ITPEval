theory putnam_1973_a2 imports Complex_Main
"HOL-Analysis.Derivative"
begin

definition putnam_1973_a2_solution :: bool where
"putnam_1973_a2_solution \<equiv> True"
theorem putnam_1973_a2:
  fixes L :: "real list"
    and pluses :: "nat"
    and S :: "nat \<Rightarrow> real"
  defines "pluses \<equiv> card {i :: nat. i \<in> {0..7} \<and> L!i = 1}"
    and "S \<equiv> \<lambda> n :: nat. (\<Sum> i \<in> {1..n}. L!(i mod 8)/(i::real))"
  assumes hlength : "length L = 8"
    and hsigns : "\<forall> i < 8. L!i = 1 \<or> L!i = -1"
  shows "(pluses = 4 \<longrightarrow> (\<exists> l :: real. filterlim S (nhds l) at_top)) \<and>
    (putnam_1973_a2_solution \<longleftrightarrow> ((\<exists> l :: real. filterlim S (nhds l) at_top) \<longrightarrow> pluses = 4))"
  sorry

end
