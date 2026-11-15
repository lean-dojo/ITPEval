theory power_FastExponentiation_fast_exp_imperativeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
theorem fast_exp_imperative'vc:
  fixes n :: "int"
  fixes x :: "int"
  assumes fact0: "(0 :: int) \<le> n"
  shows "(0 :: int) \<le> n"
  and "(1 :: int) * x ^\<^sub>i n = x ^\<^sub>i n"
  and "\<forall>(e :: int) (p :: int) (r :: int). (0 :: int) \<le> e \<and> r * p ^\<^sub>i e = x ^\<^sub>i n \<longrightarrow> (if (0 :: int) < e then \<not>(2 :: int) = (0 :: int) \<and> (if e cmod (2 :: int) = (1 :: int) then \<not>(2 :: int) = (0 :: int) \<and> ((0 :: int) \<le> e \<and> e cdiv (2 :: int) < e) \<and> (0 :: int) \<le> e cdiv (2 :: int) \<and> r * p * (p * p) ^\<^sub>i (e cdiv (2 :: int)) = x ^\<^sub>i n else \<not>(2 :: int) = (0 :: int) \<and> ((0 :: int) \<le> e \<and> e cdiv (2 :: int) < e) \<and> (0 :: int) \<le> e cdiv (2 :: int) \<and> r * (p * p) ^\<^sub>i (e cdiv (2 :: int)) = x ^\<^sub>i n) else r = x ^\<^sub>i n)"
  sorry
end
