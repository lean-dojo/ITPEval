theory strncmp_Why3_ide_VCstrncmp_len_diff_post_2_goal23
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strnlen_A_Strnlen" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal23:
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i :: "int"
  shows "let x :: int = offset a_1; x_1 :: int = offset a_2; x_2 :: int = offset a; x_3 :: int = offset a_3; x_4 :: int = i_1 + x - x_2; x_5 :: int = l_strnlen t_1 a_1 i_1; x_6 :: int = x + x_5; x_7 :: int = l_strnlen t_1 a_3 i_1; x_8 :: int = i_1 + x in x + x_1 = x_2 + x_3 \<longrightarrow> x_2 + l_strnlen t_1 a x_4 = x_6 \<longrightarrow> x_1 + l_strnlen t_1 a_2 x_4 = x_3 + x_7 \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> x \<le> x_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> x_5 < x_7 \<longrightarrow> x_2 \<le> x_8 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i_2 \<longrightarrow> is_uint8 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> p_valid_strn t t_1 a_1 i_1 \<longrightarrow> p_valid_strn t t_1 a_3 i_1 \<longrightarrow> is_uint64 x_4 \<longrightarrow> addr_le a (shift a_1 x_5) \<longrightarrow> addr_le a_2 (shift a_3 x_7) \<longrightarrow> p_valid_strn t t_1 a x_4 \<longrightarrow> p_valid_strn t t_1 a_2 x_4 \<longrightarrow> (if x_8 = x_2 then i = (0 :: int) else to_uint8 (t_1 a) = i_2 \<and> to_uint8 (t_1 a_2) = i_3 \<and> (if i_3 = i_2 then i = (0 :: int) \<and> i_3 = (0 :: int) else if i_3 < i_2 then i = -(1 :: int) else i = (1 :: int)) \<and> (i_2 = (0 :: int) \<longrightarrow> x_5 = l_strlen t_1 a_1 \<and> x_6 = x_2 \<and> p_valid_str t t_1 a_1) \<and> (i_3 = (0 :: int) \<longrightarrow> x_7 = l_strlen t_1 a_3 \<and> x + x_7 = x_2 \<and> p_valid_str t t_1 a_3)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < x_7 \<longrightarrow> t_1 (shift a_3 i_4) = t_1 (shift a_1 i_4)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + x < x_2 \<longrightarrow> t_1 (shift a_3 i_4) = t_1 (shift a_1 i_4)) \<longrightarrow> (\<forall>(i_4 :: int). let x_9 :: int = t_1 (shift a_3 i_4); x_10 :: int = t_1 (shift a_1 i_4) in (0 :: int) \<le> i_4 \<longrightarrow> i_4 < x_7 \<longrightarrow> to_uint8 x_9 = to_uint8 x_10 \<longleftrightarrow> x_9 = x_10) \<longrightarrow> i = (1 :: int)"
  sorry
end
