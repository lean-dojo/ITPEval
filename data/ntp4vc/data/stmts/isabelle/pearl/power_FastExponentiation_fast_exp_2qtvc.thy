theory power_FastExponentiation_fast_exp_2qtvc
  imports "NTP4Verif.NTP4Verif"
begin
theorem fast_exp_2'vc:
  fixes n :: "int"
  fixes acc :: "int"
  fixes x :: "int"
  assumes fact0: "(0 :: int) \<le> n"
  shows "\<not>n = (0 :: int) \<longrightarrow> \<not>(2 :: int) = (0 :: int) \<and> (if n cmod (2 :: int) = (0 :: int) then \<not>(2 :: int) = (0 :: int) \<and> (let o1 :: int = n cdiv (2 :: int) in ((0 :: int) \<le> n \<and> o1 < n) \<and> (0 :: int) \<le> o1) else let o1 :: int = n - (1 :: int) in ((0 :: int) \<le> n \<and> o1 < n) \<and> (0 :: int) \<le> o1)"
  and "\<forall>(result :: int). (if n = (0 :: int) then result = acc else if n cmod (2 :: int) = (0 :: int) then result = (x * x) ^\<^sub>i (n cdiv (2 :: int)) * acc else result = x ^\<^sub>i (n - (1 :: int)) * (x * acc)) \<longrightarrow> result = x ^\<^sub>i n * acc"
  sorry
end
