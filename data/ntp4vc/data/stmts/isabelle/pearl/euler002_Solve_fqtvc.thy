theory euler002_Solve_fqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Fibonacci" "./euler002_FibSumEven" "./euler002_FibOnlyEven"
begin
theorem f'vc:
  fixes m :: "int"
  assumes fact0: "(0 :: int) \<le> m"
  shows "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) = fib_even (0 :: int)"
  and "(0 :: int) = fib (0 :: int)"
  and "(2 :: int) = fib_even ((0 :: int) + (1 :: int))"
  and "(2 :: int) = fib ((0 :: int) + (3 :: int))"
  and "(0 :: int) = fib_sum_even m (0 :: int)"
  and "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) < (2 :: int)"
  and "\<forall>(k :: int) (n :: int). (0 :: int) \<le> n \<and> (0 :: int) \<le> k \<and> fib_even n = fib k \<and> fib_even (n + (1 :: int)) = fib (k + (3 :: int)) \<and> (0 :: int) \<le> fib_even n \<and> fib_even n < fib_even (n + (1 :: int)) \<longrightarrow> (if fib_even n \<le> m then ((0 :: int) \<le> m - fib_even n \<and> m - fib_even (n + (1 :: int)) < m - fib_even n) \<and> (0 :: int) \<le> n + (1 :: int) \<and> (0 :: int) \<le> k + (3 :: int) \<and> fib_even (n + (1 :: int)) = fib (k + (3 :: int)) \<and> (4 :: int) * fib_even (n + (1 :: int)) + fib_even n = fib_even (n + (1 :: int) + (1 :: int)) \<and> (4 :: int) * fib_even (n + (1 :: int)) + fib_even n = fib (k + (3 :: int) + (3 :: int)) \<and> fib_sum_even m k + fib_even n = fib_sum_even m (k + (3 :: int)) \<and> (0 :: int) \<le> fib_even (n + (1 :: int)) \<and> fib_even (n + (1 :: int)) < (4 :: int) * fib_even (n + (1 :: int)) + fib_even n else \<exists>(n1 :: int). fib_sum_even m k = fib_sum_even m n1 \<and> m < fib n1)"
  sorry
end
