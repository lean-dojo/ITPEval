theory strnchr_Why3_ide_VCstrnchr_loop_inv_5_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strnlen_A_Strnlen" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal6:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = to_sint8 i_1; x_2 :: int = offset a_1; x_3 :: int = offset a; x_4 :: int = i + x_3 - x_2; x_5 :: int = l_strnlen t_1 a_1 x_4; x_6 :: int = x_2 + x_5 in \<not>i = (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> x_6 = x_3 + l_strnlen t_1 a i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_2 \<le> x_3 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_strn t t_1 a i \<longrightarrow> is_uint64 x_4 \<longrightarrow> p_valid_strn t t_1 a_1 x_4 \<longrightarrow> addr_le a (shift a_1 x_5) \<longrightarrow> (\<forall>(a_2 :: addr). addr_lt a_2 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> \<not>t_1 a_2 = x_1) \<longrightarrow> x_6 = (1 :: int) + x_3 + l_strnlen t_1 (shift a (1 :: int)) (to_uint64 (i - (1 :: int)))"
  sorry
end
