theory strncmp_Why3_ide_VCstrncmp_loop_inv_5_preserved_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strnlen_A_Strnlen" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal11:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_1; x_1 :: int = to_uint8 x; x_2 :: int = t_1 a_3; x_3 :: int = offset a; x_4 :: int = i + x_3; x_5 :: int = offset a_1; x_6 :: int = offset a_2; x_7 :: int = offset a_3; x_8 :: int = x_7 - x_6; x_9 :: int = t_1 (shift a_2 x_8); x_10 :: int = t_1 (shift a x_8); x_12 :: int = i + x_3 - x_5; x_13 :: int = l_strnlen t_1 a i; x_14 :: int = l_strnlen t_1 a_2 i; x_15 :: int = to_uint64 (i + x_3 - (1 :: int) - x_5) in \<not>x_1 = (0 :: int) \<longrightarrow> to_uint8 x_2 = x_1 \<longrightarrow> \<not>x_4 = x_5 \<longrightarrow> x_5 + x_6 = x_3 + x_7 \<longrightarrow> x_9 = x_10 \<longrightarrow> x_5 + l_strnlen t_1 a_1 x_12 = x_3 + x_13 \<longrightarrow> x_7 + l_strnlen t_1 a_3 x_12 = x_6 + x_14 \<longrightarrow> x_3 \<le> x_5 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_5 \<le> x_4 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_strn t t_1 a i \<longrightarrow> p_valid_strn t t_1 a_2 i \<longrightarrow> is_uint64 x_12 \<longrightarrow> addr_le a_1 (shift a x_13) \<longrightarrow> addr_le a_3 (shift a_2 x_14) \<longrightarrow> is_sint8 x_10 \<longrightarrow> is_sint8 x_9 \<longrightarrow> p_valid_strn t t_1 a_1 x_12 \<longrightarrow> p_valid_strn t t_1 a_3 x_12 \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_3 < x_5 \<longrightarrow> t_1 (shift a_2 i_1) = t_1 (shift a i_1)) \<longrightarrow> (\<forall>(i_1 :: int). let x_16 :: int = t_1 (shift a_2 i_1); x_17 :: int = t_1 (shift a i_1) in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x_14 \<longrightarrow> to_uint8 x_16 = to_uint8 x_17 \<longleftrightarrow> x_16 = x_17) \<longrightarrow> p_valid_strn t t_1 (shift a_1 (1 :: int)) x_15 \<and> p_valid_strn t t_1 (shift a_3 (1 :: int)) x_15"
  sorry
end
