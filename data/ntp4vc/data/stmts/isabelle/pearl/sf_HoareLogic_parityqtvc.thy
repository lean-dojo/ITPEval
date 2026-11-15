theory sf_HoareLogic_parityqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
inductive even :: "int \<Rightarrow> bool" where
   even_0: "even (0 :: int)"
 | even_odd: "even x \<Longrightarrow> even (x + (2 :: int))" for x :: "int"
theorem parity'vc:
  fixes x :: "int"
  assumes fact0: "(0 :: int) \<le> x"
  shows "(0 :: int) \<le> x"
  and "even (x - x) \<or> (0 :: int) = (1 :: int) \<and> even (x - x + (1 :: int))"
  and "\<forall>(y :: int) (x1 :: int). (0 :: int) \<le> x1 \<and> (y = (0 :: int) \<and> even (x - x1) \<or> y = (1 :: int) \<and> even (x - x1 + (1 :: int))) \<longrightarrow> (if \<not>x1 = (0 :: int) then ((0 :: int) \<le> x1 \<and> x1 - (1 :: int) < x1) \<and> (0 :: int) \<le> x1 - (1 :: int) \<and> ((1 :: int) - y = (0 :: int) \<and> even (x - (x1 - (1 :: int))) \<or> (1 :: int) - y = (1 :: int) \<and> even (x - (x1 - (1 :: int)) + (1 :: int))) else y = (0 :: int) \<longleftrightarrow> even x)"
  sorry
end
