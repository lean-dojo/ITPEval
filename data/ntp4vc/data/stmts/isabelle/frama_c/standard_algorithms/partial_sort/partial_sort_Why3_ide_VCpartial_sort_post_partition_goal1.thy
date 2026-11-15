theory partial_sort_Why3_ide_VCpartial_sort_post_partition_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal1:
  fixes a :: "addr"
  fixes t_6 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes p :: "bool"
  fixes t_1 :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_8 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes t_7 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); x :: int = t_6 a_1; a_2 :: addr \<Rightarrow> int = havoc t_3 t_5 a_1 i_2 in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 (t_5 a_1) \<longrightarrow> is_sint32 x \<longrightarrow> valid_rw t a_1 i \<longrightarrow> (if (0 :: int) < i_1 then p = False \<and> t_1 = t \<and> havoc t_2 t_8 a_1 i_1 = t_5 \<and> havoc t_3 t_5 a_1 i = t_6 \<and> havoc t_4 a_2 a_1 i_1 = t_7 \<and> i_2 \<le> i \<and> i \<le> i_2 \<and> i_1 \<le> i_2 \<and> p_sorted_1' t_7 a (0 :: int) i_1 \<and> p_isheap t_5 a i_1 \<and> p_isheap t_6 a i_1 \<and> p_multisetunchanged_1' t_5 t_8 a (0 :: int) i_1 \<and> p_multisetunchanged_1' t_6 t_8 a (0 :: int) i_2 \<and> p_unchanged_1' t_6 t_8 a i_2 i \<and> valid_rw t_1 a_1 i_1 \<and> p_upperbound_1' t_6 a (0 :: int) i_1 x \<and> p_lowerbound_1' t_6 a i_1 i_2 x \<and> p_multisetunchanged_1' t_7 a_2 a (0 :: int) i_1 else t_8 = t_7) \<longrightarrow> p_partition t_7 a i_1 i"
  sorry
end
