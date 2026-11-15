theory binary_sqrt_BinarySqrt_sqrtqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.real_Truncate"
begin
theorem sqrt'vc:
  fixes r :: "real"
  fixes eps0 :: "real"
  fixes n :: "int"
  fixes o1 :: "bool"
  assumes fact0: "(0 :: Real.real) \<le> r"
  assumes fact1: "(0 :: Real.real) < eps0"
  assumes fact2: "(1 :: int) \<le> n"
  assumes fact3: "if r < real_of_int n * eps0 then o1 = (if (1 :: Real.real) < real_of_int n * eps0 then True else False) else o1 = False"
  shows "\<not>o1 = True \<longrightarrow> (let o2 :: int = (2 :: int) * n in ((0 :: int) \<le> ceil (max r (1 :: Real.real) / eps0) - n \<and> ceil (max r (1 :: Real.real) / eps0) - o2 < ceil (max r (1 :: Real.real) / eps0) - n) \<and> (0 :: Real.real) \<le> r \<and> ((0 :: Real.real) < eps0 \<and> (1 :: int) \<le> o2) \<and> (2 :: Real.real) * (real_of_int n * eps0) = real_of_int o2 * eps0)"
  and "\<forall>(result :: real). (if o1 = True then result = (0 :: Real.real) else let o2 :: real = (2 :: Real.real) * (real_of_int n * eps0) in \<exists>(r' :: real). (r' * r' \<le> r \<and> r < (r' + o2) * (r' + o2)) \<and> (if (r' + real_of_int n * eps0) * (r' + real_of_int n * eps0) \<le> r then result = r' + real_of_int n * eps0 else result = r')) \<longrightarrow> result * result \<le> r \<and> r < (result + real_of_int n * eps0) * (result + real_of_int n * eps0)"
  sorry
end
