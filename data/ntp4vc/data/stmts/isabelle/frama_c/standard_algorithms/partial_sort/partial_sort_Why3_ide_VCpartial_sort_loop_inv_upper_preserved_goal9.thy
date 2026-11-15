theory partial_sort_Why3_ide_VCpartial_sort_loop_inv_upper_preserved_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal9:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_5 a_1 i_2; a_3 :: addr \<Rightarrow> int = havoc t_2 a_2 a_1 i_1; a_4 :: addr \<Rightarrow> int = havoc t_3 a_3 a_1 i_2; x :: int = i_2 - (1 :: int); a_5 :: addr = shift a x; a_6 :: int = a_4 a_5; a_7 :: int = a_3 a_1; a_8 :: addr = shift a i_3; a_9 :: int = a_4 a_8; a_10 :: addr \<Rightarrow> int = a_4(a_5 := a_9, a_8 := i); a_11 :: int = a_10 a_8; a_12 :: int = a_3 a_8; x_1 :: int = (1 :: int) + i_3; a_13 :: addr \<Rightarrow> int = havoc t_4 a_10 a_1 i_2; a_14 :: int = a_13 a_1 in a_6 = a_7 \<longrightarrow> a_11 = a_6 \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_3 < i_1 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> a_12 < a_7 \<longrightarrow> i_3 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_8 (1 :: int) \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> valid_rw t a_1 i_2 \<longrightarrow> valid_rw t a_8 (1 :: int) \<longrightarrow> valid_rw t a_5 (1 :: int) \<longrightarrow> is_sint32 (a_2 a_1) \<longrightarrow> p_isheap a_2 a i_2 \<longrightarrow> p_multisetunchanged_1' a_2 t_5 a (0 :: int) i_2 \<longrightarrow> is_sint32 a_7 \<longrightarrow> is_sint32 a_12 \<longrightarrow> p_isheap a_3 a i_2 \<longrightarrow> p_multisetunchanged_1' a_3 t_5 a (0 :: int) i_3 \<longrightarrow> p_unchanged_1' a_3 t_5 a i_3 i_1 \<longrightarrow> p_upperbound_1' a_3 a (0 :: int) i_2 a_7 \<longrightarrow> p_lowerbound_1' a_3 a i_2 i_3 a_7 \<longrightarrow> is_sint32 a_9 \<longrightarrow> is_sint32 a_6 \<longrightarrow> p_isheap a_4 a x \<longrightarrow> is_sint32 a_11 \<longrightarrow> p_multisetunchanged_1' a_4 t_5 a (0 :: int) x_1 \<longrightarrow> p_multisetunchanged_1' a_4 a_3 a (0 :: int) i_2 \<longrightarrow> p_maxelement a_4 a i_2 x \<longrightarrow> p_isheap a_10 a x \<longrightarrow> p_multisetunchanged_1' a_10 a_4 a (0 :: int) x_1 \<longrightarrow> p_unchanged_1' a_10 a_4 a x_1 i_1 \<longrightarrow> p_swappedinside a_10 a_4 a x i_3 x_1 \<longrightarrow> is_sint32 a_14 \<longrightarrow> p_isheap a_13 a i_2 \<longrightarrow> p_multisetunchanged_1' a_13 a_10 a (0 :: int) i_2 \<longrightarrow> p_multisetunchanged_1' a_13 a_10 a (0 :: int) x_1 \<longrightarrow> p_lowerbound_1' a_13 a i_2 x_1 a_14 \<longrightarrow> p_upperbound_1' a_13 a (0 :: int) i_2 a_14"
  sorry
end
