theory strncmp_Why3_ide_VCstrncmp_loop_inv_3_preserved_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strnlen_A_Strnlen" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal8:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_1; x_1 :: int = to_uint8 x; x_2 :: int = t_1 a_3; x_3 :: int = offset a_1; x_4 :: int = offset a_2; x_5 :: int = offset a; x_6 :: int = offset a_3; x_7 :: int = x_6 - x_4; x_8 :: int = t_1 (shift a_2 x_7); x_9 :: int = t_1 (shift a x_7); x_10 :: int = i + x_3 - x_5; x_11 :: int = l_strnlen t_1 a x_10; x_12 :: int = l_strnlen t_1 a_2 x_10; a_4 :: addr = shift a x_11; a_5 :: addr = shift a_1 (1 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> to_uint8 x_2 = x_1 \<longrightarrow> x_3 + x_4 = x_5 + x_6 \<longrightarrow> x_8 = x_9 \<longrightarrow> x_5 + x_11 = x_3 + l_strnlen t_1 a_1 i \<longrightarrow> x_4 + x_12 = x_6 + l_strnlen t_1 a_3 i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_5 \<le> x_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_strn t t_1 a_1 i \<longrightarrow> p_valid_strn t t_1 a_3 i \<longrightarrow> is_uint64 x_10 \<longrightarrow> is_sint8 x_9 \<longrightarrow> is_sint8 x_8 \<longrightarrow> p_valid_strn t t_1 a x_10 \<longrightarrow> p_valid_strn t t_1 a_2 x_10 \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> addr_le a_3 (shift a_2 x_12) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_5 < x_3 \<longrightarrow> t_1 (shift a_2 i_1) = t_1 (shift a i_1)) \<longrightarrow> (\<forall>(i_1 :: int). let x_13 :: int = t_1 (shift a_2 i_1); x_14 :: int = t_1 (shift a i_1) in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x_12 \<longrightarrow> to_uint8 x_13 = to_uint8 x_14 \<longleftrightarrow> x_13 = x_14) \<longrightarrow> addr_le a a_5 \<and> addr_le a_5 a_4"
  sorry
end
