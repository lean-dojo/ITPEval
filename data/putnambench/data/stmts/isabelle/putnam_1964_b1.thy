theory putnam_1964_b1 imports Complex_Main
"HOL-Library.Extended_Nonnegative_Real"
begin

theorem putnam_1964_b1:
  fixes a :: "nat \<Rightarrow> int"
  and b :: "nat \<Rightarrow> nat"
  assumes apos: "\<forall>k::nat. a k > 0"
  and ha: "summable (\<lambda>n::nat. 1 / real_of_int (a n))"
  defines "b \<equiv> (\<lambda>n::nat. card {k::nat. a k \<le> int n})"
  shows "filterlim (\<lambda>n::nat. real_of_nat (b n) / real_of_nat n) (nhds 0) at_top"
  sorry

end
