theory equal_range_Why3_ide_VCequal_range_post_result_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/S1_size_type_pair_S1_size_type_pair" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Compound_Compound"
begin
theorem goal0:
  fixes s :: "s1_size_type_pair"
  fixes i_8 :: "int"
  fixes i_10 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_7 :: "int"
  fixes i_11 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes i_6 :: "int"
  fixes i_9 :: "int"
  fixes i :: "int"
  fixes p_1 :: "bool"
  fixes p_2 :: "bool"
  fixes p_3 :: "bool"
  fixes p :: "bool"
  shows "let x :: int = f1_size_type_pair_first s; x_2 :: int = i_8 - i_10; x_3 :: int = x_2 cdiv (2 :: int); x_4 :: int = i_10 + x_3; x_5 :: int = f1_size_type_pair_second s; a_1 :: addr = shift a x_4; x_6 :: int = t_1 a_1; x_7 :: int = i_10 + to_uint32 (to_uint32 x_2 cdiv (2 :: int)); a_2 :: addr = shift a i_10; a_3 :: addr = shift a ((1 :: int) + i_10 + x_3); x_9 :: int = i_8 - (1 :: int) - i_10 - x_3; x_10 :: int = x - i_10; x_11 :: int = x_5 - (1 :: int) - i_10 - x_3 in i_8 \<le> i_7 \<longrightarrow> i_11 \<le> i_8 \<longrightarrow> (0 :: int) \<le> i_11 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> iss1_size_type_pair s \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_uint32 i_6 \<longrightarrow> is_uint32 i_7 \<longrightarrow> is_uint32 i_8 \<longrightarrow> is_uint32 i_9 \<longrightarrow> is_uint32 i_10 \<longrightarrow> is_uint32 i_11 \<longrightarrow> is_sint32 i \<longrightarrow> p_sorted_1' t_1 a (0 :: int) i_7 \<longrightarrow> p_strictupperbound_1' t_1 a (0 :: int) i_11 i \<longrightarrow> p_strictlowerbound_1' t_1 a i_8 i_7 i \<longrightarrow> valid_rd t (shift a (0 :: int)) i_7 \<longrightarrow> (if i_11 < i_8 then p_1 = False \<and> p_2 = False \<and> p_3 = False \<and> i_2 = i_1 \<and> i_5 = i_4 \<and> i_10 = i_9 \<and> i_11 = i_10 \<and> x = i_3 + i_10 \<and> x = i_6 + i_10 \<and> x_4 = i_4 \<and> x_4 = i_5 \<and> x_5 = (1 :: int) + i_1 + i_10 + x_3 \<and> x_5 = (1 :: int) + i_2 + i_10 + x_3 \<and> x_5 \<le> i_8 \<and> (0 :: int) \<le> x \<and> i_10 \<le> x \<and> (0 :: int) \<le> x_5 \<and> (0 :: int) \<le> x_3 \<and> x_4 < i_8 \<and> x \<le> x_4 \<and> x_4 < x_5 \<and> x_6 \<le> i \<and> (0 :: int) \<le> x_7 \<and> i \<le> x_6 \<and> x \<le> (4294967295 :: int) \<and> x_5 \<le> (4294967295 :: int) \<and> i_8 \<le> (4294967295 :: int) + i_10 \<and> x_3 \<le> (4294967295 :: int) \<and> x_4 \<le> (4294967294 :: int) \<and> i_8 \<le> (4294967296 :: int) + i_10 + x_3 \<and> x_7 \<le> (4294967295 :: int) \<and> valid_rd t a_2 x_3 \<and> p_sorted_1' t_1 a_2 (0 :: int) x_3 \<and> valid_rd t a_1 (1 :: int) \<and> valid_rd t a_3 x_9 \<and> p_sorted_1' t_1 a_3 (0 :: int) x_9 \<and> p_strictupperbound_1' t_1 a_2 (0 :: int) x_10 x_6 \<and> p_strictlowerbound_1' t_1 a_3 x_11 x_9 x_6 \<and> p_lowerbound_1' t_1 a_2 x_10 x_3 x_6 \<and> p_upperbound_1' t_1 a_3 (0 :: int) x_11 x_6 else p = False \<and> x = i_11 \<and> x_5 = x) \<longrightarrow> x_5 \<le> i_7 \<and> (0 :: int) \<le> x \<and> x \<le> x_5"
  sorry
end
