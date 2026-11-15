theory putnam_1969_b5 imports Complex_Main
begin

theorem putnam_1969_b5:
  fixes a :: "nat \<Rightarrow> nat"
  and k :: "nat \<Rightarrow> nat"
  assumes ha: "strict_mono a \<and> (\<forall>n::nat. a n > 0)"
  and hinvasum: "\<exists>C::real. filterlim (\<lambda>n::nat. (\<Sum>i\<in>{..<n}. 1 / real_of_nat (a i))) (nhds C) at_top"
  defines "k \<equiv> (\<lambda>x::nat. card {n::nat. a n \<le> x})"
  shows "filterlim (\<lambda>t::nat. real_of_nat (k t) / real_of_nat t) (nhds 0) at_top"
  sorry

end
