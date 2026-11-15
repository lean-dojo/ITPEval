theory largest_prime_factor_PrimeFactor_smallest_divisorqtvc
  imports "NTP4Verif.NTP4Verif"
begin
theorem smallest_divisor'vc:
  fixes n :: "int"
  fixes d :: "int"
  assumes fact0: "(2 :: int) \<le> n"
  assumes fact1: "(2 :: int) \<le> d"
  assumes fact2: "d \<le> n"
  assumes fact3: "\<forall>(i :: int). (2 :: int) \<le> i \<and> i < d \<longrightarrow> \<not>i dvd n"
  shows "let o1 :: int = d * d in (\<not>n < o1 \<longrightarrow> ((2 :: int) \<le> d \<longrightarrow> \<not>d = (0 :: int)) \<and> (\<forall>(o2 :: bool). (if (2 :: int) \<le> d then o2 = (if n cmod d = (0 :: int) then True else False) else o2 = False) \<longrightarrow> \<not>o2 = True \<longrightarrow> (let o3 :: int = d + (1 :: int) in ((0 :: int) \<le> n - d \<and> n - o3 < n - d) \<and> (2 :: int) \<le> n \<and> ((2 :: int) \<le> o3 \<and> o3 \<le> n) \<and> (\<forall>(i :: int). (2 :: int) \<le> i \<and> i < o3 \<longrightarrow> \<not>i dvd n)))) \<and> (\<forall>(result :: int). (if n < o1 then result = n else \<exists>(o2 :: bool). (if (2 :: int) \<le> d then o2 = (if n cmod d = (0 :: int) then True else False) else o2 = False) \<and> (if o2 = True then result = d else (d + (1 :: int) \<le> result \<and> result \<le> n) \<and> result dvd n \<and> (\<forall>(i :: int). (2 :: int) \<le> i \<and> i < result \<longrightarrow> \<not>i dvd n))) \<longrightarrow> (d \<le> result \<and> result \<le> n) \<and> result dvd n \<and> (\<forall>(i :: int). (2 :: int) \<le> i \<and> i < result \<longrightarrow> \<not>i dvd n))"
  sorry
end
