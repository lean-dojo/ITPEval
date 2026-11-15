theory strchr_Why3_ide_VCstrchr_assert_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strchr_A_Strchr" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal7:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; a_2 :: addr = shift a_1 (l_strlen t_1 a_1) in x = to_sint8 i \<longrightarrow> l_strchr t_1 a_1 x = l_strchr t_1 a x \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_le a a_2 \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> \<not>x = t_1 a_3) \<longrightarrow> addr_lt a a_2 \<longleftrightarrow> \<not>x = (0 :: int)"
  sorry
end
