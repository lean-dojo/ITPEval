theory word_common_factor_Top_powerqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  char
theorem power'vc:
  fixes n :: "int"
  assumes fact0: "(0 :: int) \<le> n"
  assumes fact1: "\<not>n = (0 :: int)"
  shows "let o1 :: int = n - (1 :: int) in ((0 :: int) \<le> n \<and> o1 < n) \<and> (0 :: int) \<le> o1"
  sorry
end
