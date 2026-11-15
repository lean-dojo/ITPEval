theory sf_HoareLogic_slow_additionqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
theorem slow_addition'vc:
  fixes x :: "int"
  fixes z1 :: "int"
  assumes fact0: "(0 :: int) \<le> x"
  shows "(0 :: int) \<le> x"
  and "\<forall>(z :: int) (x1 :: int). (0 :: int) \<le> x1 \<and> z + x1 = z1 + x \<longrightarrow> (if \<not>x1 = (0 :: int) then ((0 :: int) \<le> x1 \<and> x1 - (1 :: int) < x1) \<and> (0 :: int) \<le> x1 - (1 :: int) \<and> z + (1 :: int) + (x1 - (1 :: int)) = z1 + x else z = z1 + x)"
  sorry
end
