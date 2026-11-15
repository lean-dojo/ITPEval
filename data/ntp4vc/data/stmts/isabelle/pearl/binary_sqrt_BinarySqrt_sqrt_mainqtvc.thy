theory binary_sqrt_BinarySqrt_sqrt_mainqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.real_Truncate"
begin
theorem sqrt_main'vc:
  fixes r :: "real"
  fixes eps :: "real"
  assumes fact0: "(0 :: Real.real) \<le> r"
  assumes fact1: "(0 :: Real.real) < eps"
  shows "(0 :: Real.real) \<le> r"
  and "(0 :: Real.real) < eps"
  and "(1 :: int) \<le> (1 :: int)"
  and "eps = real_of_int (1 :: int) * eps"
  sorry
end
