theory strpbrk_Why3_ide_VCstrpbrk_loop_inv_3_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_StrPBrk_A_StrPBrk" "../../lib/isabelle/A_StrSpn_A_StrSpn" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  shows "let x :: int = t_1 a_1; a_6 :: addr = shift a_2 (l_strlen t_1 a_2) in t_1 a = (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> l_strpbrk a_3 a_2 = l_strpbrk a_1 a_2 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_2 a_4 \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> addr_le a_3 a_5 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> addr_lt a_5 (shift a_1 (1 :: int)) \<longrightarrow> addr_lt a_4 a_6 \<longrightarrow> addr_le a a_6 \<longrightarrow> addr_le a_1 (shift a_3 (l_strlen t_1 a_3)) \<longrightarrow> (p_in_array t_1 a_2 x \<longrightarrow> p_in_array t_1 a x) \<longrightarrow> (\<forall>(a_7 :: addr). addr_lt a_7 a \<longrightarrow> addr_le a_2 a_7 \<longrightarrow> \<not>x = t_1 a_7) \<longrightarrow> (\<forall>(a_7 :: addr). addr_le a_2 a_7 \<longrightarrow> addr_lt a_7 a_6 \<longrightarrow> \<not>x = t_1 a_7) \<longrightarrow> (\<forall>(a_8 :: addr) (a_7 :: addr). addr_lt a_8 a_1 \<longrightarrow> addr_le a_2 a_7 \<longrightarrow> addr_le a_3 a_8 \<longrightarrow> addr_lt a_7 a_6 \<longrightarrow> \<not>t_1 a_8 = t_1 a_7) \<longrightarrow> (\<forall>(a_8 :: addr) (a_7 :: addr). addr_le a_8 a_1 \<longrightarrow> addr_le a_2 a_7 \<longrightarrow> addr_le a_3 a_8 \<longrightarrow> addr_lt a_7 a_6 \<longrightarrow> \<not>t_1 a_8 = t_1 a_7) \<longrightarrow> \<not>t_1 a_5 = t_1 a_4"
  sorry
end
