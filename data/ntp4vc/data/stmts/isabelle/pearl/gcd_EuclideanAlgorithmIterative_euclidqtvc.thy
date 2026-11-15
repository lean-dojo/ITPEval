theory gcd_EuclideanAlgorithmIterative_euclidqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
theorem euclid'vc:
  fixes u0 :: "int"
  fixes v0 :: "int"
  assumes fact0: "(0 :: int) \<le> u0"
  assumes fact1: "(0 :: int) \<le> v0"
  shows "(0 :: int) \<le> u0"
  and "(0 :: int) \<le> v0"
  and "\<forall>(v :: int) (u :: int). ((0 :: int) \<le> u \<and> (0 :: int) \<le> v) \<and> gcd u v = gcd u0 v0 \<longrightarrow> (if \<not>v = (0 :: int) then \<not>v = (0 :: int) \<and> ((0 :: int) \<le> v \<and> u cmod v < v) \<and> ((0 :: int) \<le> v \<and> (0 :: int) \<le> u cmod v) \<and> gcd v (u cmod v) = gcd u0 v0 else u = gcd u0 v0)"
  sorry
end
