theory strspn_Why3_ide_VCstrspn_post_2_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_StrSpn_A_StrSpn" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_5 :: "addr"
  fixes a_4 :: "addr"
  shows "let x :: int = offset a_1; x_1 :: int = offset a; x_2 :: int = l_strlen t_1 a; x_3 :: int = t_1 a_1; x_4 :: int = t_1 a_2; a_6 :: addr = shift a_3 (l_strlen t_1 a_3); x_5 :: int = i + x_1 in x + l_strspn a_1 a_3 = x_1 + l_strspn a a_3 \<longrightarrow> x_1 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> x \<le> x_1 + x_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_3 a_5 \<longrightarrow> is_sint8 x_3 \<longrightarrow> is_sint8 x_4 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> is_uint64 (x - x_1) \<longrightarrow> addr_lt a_5 a_6 \<longrightarrow> addr_le a_1 (shift a x_2) \<longrightarrow> (if x_3 = (0 :: int) then x_5 = x else a_2 = a_1 \<and> t_1 a_4 = (0 :: int) \<and> x_5 = offset a_2 \<and> addr_le a_3 a_4 \<and> p_valid_str t t_1 a_4 \<and> \<not>p_in_array t_1 a_3 x_4 \<and> addr_le a_4 a_6 \<and> (\<forall>(a_7 :: addr). addr_lt a_7 a_4 \<longrightarrow> addr_le a_3 a_7 \<longrightarrow> \<not>x_4 = t_1 a_7)) \<longrightarrow> (\<forall>(a_7 :: addr). addr_lt a_7 a_1 \<longrightarrow> addr_le a a_7 \<longrightarrow> (\<exists>(a_8 :: addr). t_1 a_7 = t_1 a_8 \<and> addr_le a_3 a_8 \<and> addr_lt a_8 a_6)) \<longrightarrow> \<not>t_1 (shift a i) = t_1 a_5"
  sorry
end
