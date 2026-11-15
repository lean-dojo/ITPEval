theory sf_HoareLogic_reduce_to_zeroqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
theorem reduce_to_zero'vc:
  fixes x :: "int"
  assumes fact0: "(0 :: int) \<le> x"
  shows "(0 :: int) \<le> x"
  and "\<forall>(x1 :: int). (0 :: int) \<le> x1 \<longrightarrow> (if \<not>x1 = (0 :: int) then ((0 :: int) \<le> x1 \<and> x1 - (1 :: int) < x1) \<and> (0 :: int) \<le> x1 - (1 :: int) else x1 = (0 :: int))"
  sorry
end
