theory strchrnul_Why3_ide_VCstrchrnul_loop_inv_3_preserved_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strchrnul_A_Strchrnul" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal5:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  shows "let x :: int = t_1 a; x_1 :: int = to_sint8 i in \<not>x = (0 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> l_strchrnul t_1 a_1 x_1 = l_strchrnul t_1 a x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_lt a_2 (shift a (1 :: int)) \<longrightarrow> addr_le a (shift a_1 (l_strlen t_1 a_1)) \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> \<not>t_1 a_3 = x_1) \<longrightarrow> \<not>t_1 a_2 = x_1"
  sorry
end
