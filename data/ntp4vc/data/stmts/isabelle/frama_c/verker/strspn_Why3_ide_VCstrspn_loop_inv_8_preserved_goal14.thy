theory strspn_Why3_ide_VCstrspn_loop_inv_8_preserved_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_StrSpn_A_StrSpn" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal14:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_4 :: "addr"
  shows "let x :: int = t_1 a_1; x_1 :: int = t_1 a_3; x_2 :: int = offset a_1; x_3 :: int = offset a; x_4 :: int = l_strlen t_1 a; a_5 :: addr = shift a_2 (l_strlen t_1 a_2) in \<not>x = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> \<not>x_1 = x \<longrightarrow> x_2 + l_strspn a_1 a_2 = x_3 + l_strspn a a_2 \<longrightarrow> x_3 \<le> x_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_2 \<le> x_3 + x_4 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> addr_le a_2 a_4 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> addr_lt a_4 (shift a_3 (1 :: int)) \<longrightarrow> is_uint64 (x_2 - x_3) \<longrightarrow> addr_le a_1 (shift a x_4) \<longrightarrow> addr_le a_3 a_5 \<longrightarrow> (p_in_array t_1 a_2 x \<longrightarrow> p_in_array t_1 a_3 x) \<longrightarrow> (\<forall>(a_6 :: addr). addr_lt a_6 a_3 \<longrightarrow> addr_le a_2 a_6 \<longrightarrow> \<not>x = t_1 a_6) \<longrightarrow> (\<forall>(a_6 :: addr). addr_lt a_6 a_1 \<longrightarrow> addr_le a a_6 \<longrightarrow> (\<exists>(a_7 :: addr). t_1 a_6 = t_1 a_7 \<and> addr_le a_2 a_7 \<and> addr_lt a_7 a_5)) \<longrightarrow> \<not>t_1 a_4 = x"
  sorry
end
