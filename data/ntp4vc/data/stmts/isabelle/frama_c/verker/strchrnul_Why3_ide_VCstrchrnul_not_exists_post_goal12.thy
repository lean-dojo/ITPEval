theory strchrnul_Why3_ide_VCstrchrnul_not_exists_post_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strchrnul_A_Strchrnul" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal12:
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = to_sint8 i; x_1 :: int = t_1 a; x_2 :: int = l_strlen t_1 a_1; a_2 :: addr = shift a_1 x_2 in l_strchrnul t_1 a_1 x = l_strchrnul t_1 a x \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_le a a_2 \<longrightarrow> (x_1 = (0 :: int) \<longrightarrow> offset a_1 + x_2 = offset a) \<longrightarrow> x_1 = (0 :: int) \<or> x_1 = x \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> \<not>t_1 a_3 = x) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x_2 \<longrightarrow> \<not>t_1 (shift a_1 i_1) = x) \<longrightarrow> a_2 = a"
  sorry
end
