theory strspn_Why3_ide_VCstrspn_assert_2_goal19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_StrSpn_A_StrSpn" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal19:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_1; x_1 :: int = t_1 a_3; x_2 :: int = offset a_1; x_3 :: int = offset a; x_4 :: int = l_strlen t_1 a; a_4 :: addr = shift a_2 (l_strlen t_1 a_2) in \<not>x = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> x_1 = x \<longrightarrow> x_2 + l_strspn a_1 a_2 = x_3 + l_strspn a a_2 \<longrightarrow> x_3 \<le> x_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_2 \<le> x_3 + x_4 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> is_uint64 (x_2 - x_3) \<longrightarrow> addr_le a_1 (shift a x_4) \<longrightarrow> addr_le a_3 a_4 \<longrightarrow> (p_in_array t_1 a_2 x \<longrightarrow> p_in_array t_1 a_3 x) \<longrightarrow> (\<forall>(a_5 :: addr). addr_lt a_5 a_3 \<longrightarrow> addr_le a_2 a_5 \<longrightarrow> \<not>x = t_1 a_5) \<longrightarrow> (\<forall>(a_5 :: addr). addr_lt a_5 a_1 \<longrightarrow> addr_le a a_5 \<longrightarrow> (\<exists>(a_6 :: addr). t_1 a_5 = t_1 a_6 \<and> addr_le a_2 a_6 \<and> addr_lt a_6 a_4)) \<longrightarrow> p_in_array t_1 a_2 x"
  sorry
end
