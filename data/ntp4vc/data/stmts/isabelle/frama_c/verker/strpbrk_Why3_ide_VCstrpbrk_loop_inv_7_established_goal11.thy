theory strpbrk_Why3_ide_VCstrpbrk_loop_inv_7_established_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_StrPBrk_A_StrPBrk" "../../lib/isabelle/A_StrSpn_A_StrSpn" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal11:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_3 :: "addr"
  shows "let x :: int = t_1 a in \<not>x = (0 :: int) \<longrightarrow> l_strpbrk a_2 a_1 = l_strpbrk a a_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_lt a_3 a_1 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_2 a \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> addr_le a (shift a_2 (l_strlen t_1 a_2)) \<longrightarrow> (\<forall>(a_5 :: addr) (a_4 :: addr). addr_lt a_5 a \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> addr_le a_2 a_5 \<longrightarrow> addr_lt a_4 (shift a_1 (l_strlen t_1 a_1)) \<longrightarrow> \<not>t_1 a_5 = t_1 a_4) \<longrightarrow> \<not>t_1 a_3 = x"
  sorry
end
