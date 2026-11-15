theory isqrt_NewtonMethod_sqrtqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./isqrt_Square"
begin
theorem sqrt'vc:
  fixes x :: "int"
  assumes fact0: "(0 :: int) \<le> x"
  shows "if x = (0 :: int) then isqrt_spec x (0 :: int) else if x \<le> (3 :: int) then isqrt_spec x (1 :: int) else \<not>(2 :: int) = (0 :: int) \<and> (let o1 :: int = ((1 :: int) + x) cdiv (2 :: int) in ((0 :: int) < o1 \<and> (0 :: int) < x \<and> o1 = (x cdiv x + x) cdiv (2 :: int) \<and> x < sqr (x + (1 :: int)) \<and> x < sqr (o1 + (1 :: int))) \<and> (\<forall>(y :: int). (0 :: int) < (x cdiv y + y) cdiv (2 :: int) \<and> (0 :: int) < y \<and> x < sqr (y + (1 :: int)) \<and> x < sqr ((x cdiv y + y) cdiv (2 :: int) + (1 :: int)) \<longrightarrow> (if (x cdiv y + y) cdiv (2 :: int) < y then \<not>(x cdiv y + y) cdiv (2 :: int) = (0 :: int) \<and> \<not>(2 :: int) = (0 :: int) \<and> ((0 :: int) \<le> y \<and> (x cdiv y + y) cdiv (2 :: int) < y) \<and> (0 :: int) < (x cdiv ((x cdiv y + y) cdiv (2 :: int)) + (x cdiv y + y) cdiv (2 :: int)) cdiv (2 :: int) \<and> (0 :: int) < (x cdiv y + y) cdiv (2 :: int) \<and> x < sqr ((x cdiv y + y) cdiv (2 :: int) + (1 :: int)) \<and> x < sqr ((x cdiv ((x cdiv y + y) cdiv (2 :: int)) + (x cdiv y + y) cdiv (2 :: int)) cdiv (2 :: int) + (1 :: int)) else isqrt_spec x y)))"
  sorry
end
