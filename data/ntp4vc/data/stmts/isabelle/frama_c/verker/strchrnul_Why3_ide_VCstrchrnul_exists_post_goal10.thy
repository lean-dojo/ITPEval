theory strchrnul_Why3_ide_VCstrchrnul_exists_post_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strchrnul_A_Strchrnul" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal10:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a_1 i); x_1 :: int = l_strlen t_1 a_1 in t_1 a = (0 :: int) \<longrightarrow> x = to_sint8 i_1 \<longrightarrow> offset a_1 + x_1 = offset a \<longrightarrow> l_strchrnul t_1 a_1 x = l_strchrnul t_1 a x \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_le a (shift a_1 x_1) \<longrightarrow> (\<forall>(a_2 :: addr). addr_lt a_2 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> \<not>x = t_1 a_2) \<longrightarrow> x = (0 :: int)"
  sorry
end
