theory isqrt_Simple_isqrtqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./isqrt_Square"
begin
theorem isqrt'vc:
  fixes x :: "int"
  assumes fact0: "(0 :: int) \<le> x"
  shows "(0 :: int) \<le> (0 :: int)"
  and "sqr (0 :: int) \<le> x"
  and "(1 :: int) = sqr ((0 :: int) + (1 :: int))"
  and "\<forall>(count :: int). (0 :: int) \<le> count \<and> sqr count \<le> x \<longrightarrow> (if sqr (count + (1 :: int)) \<le> x then ((0 :: int) \<le> x - count \<and> x - (count + (1 :: int)) < x - count) \<and> (0 :: int) \<le> count + (1 :: int) \<and> sqr (count + (1 :: int)) \<le> x \<and> sqr (count + (1 :: int)) + ((2 :: int) * (count + (1 :: int)) + (1 :: int)) = sqr (count + (1 :: int) + (1 :: int)) else isqrt_spec x count)"
  sorry
end
