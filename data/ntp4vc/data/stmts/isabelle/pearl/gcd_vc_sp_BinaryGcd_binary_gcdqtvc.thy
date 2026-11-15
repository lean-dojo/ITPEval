theory gcd_vc_sp_BinaryGcd_binary_gcdqtvc
  imports "NTP4Verif.NTP4Verif"
begin
theorem binary_gcd'vc:
  fixes u :: "int"
  fixes v :: "int"
  assumes fact0: "(0 :: int) \<le> u"
  assumes fact1: "(0 :: int) \<le> v"
  shows "if u < v then ((0 :: int) \<le> v \<and> u < v \<or> v = u \<and> (0 :: int) \<le> u \<and> v < u) \<and> (0 :: int) \<le> v \<and> (0 :: int) \<le> u else \<not>v = (0 :: int) \<longrightarrow> \<not>(2 :: int) = (0 :: int) \<and> (if u cmod (2 :: int) = (0 :: int) then \<not>(2 :: int) = (0 :: int) \<and> (if v cmod (2 :: int) = (0 :: int) then \<not>(2 :: int) = (0 :: int) \<and> (let o1 :: int = v cdiv (2 :: int) in \<not>(2 :: int) = (0 :: int) \<and> (let o2 :: int = u cdiv (2 :: int) in ((0 :: int) \<le> v \<and> o1 < v \<or> v = o1 \<and> (0 :: int) \<le> u \<and> o2 < u) \<and> (0 :: int) \<le> o2 \<and> (0 :: int) \<le> o1)) else \<not>(2 :: int) = (0 :: int) \<and> (let o1 :: int = u cdiv (2 :: int) in ((0 :: int) \<le> u \<and> o1 < u) \<and> (0 :: int) \<le> o1 \<and> (0 :: int) \<le> v)) else \<not>(2 :: int) = (0 :: int) \<and> (if v cmod (2 :: int) = (0 :: int) then \<not>(2 :: int) = (0 :: int) \<and> (let o1 :: int = v cdiv (2 :: int) in ((0 :: int) \<le> v \<and> o1 < v) \<and> (0 :: int) \<le> u \<and> (0 :: int) \<le> o1) else \<not>(2 :: int) = (0 :: int) \<and> (let o1 :: int = (u - v) cdiv (2 :: int) in ((0 :: int) \<le> u \<and> o1 < u) \<and> (0 :: int) \<le> o1 \<and> (0 :: int) \<le> v)))"
  and "\<forall>(result :: int). (if u < v then result = gcd v u else if v = (0 :: int) then result = u else if u cmod (2 :: int) = (0 :: int) then if v cmod (2 :: int) = (0 :: int) then result = (2 :: int) * gcd (u cdiv (2 :: int)) (v cdiv (2 :: int)) else result = gcd (u cdiv (2 :: int)) v else if v cmod (2 :: int) = (0 :: int) then result = gcd u (v cdiv (2 :: int)) else result = gcd ((u - v) cdiv (2 :: int)) v) \<longrightarrow> result = gcd u v"
  sorry
end
