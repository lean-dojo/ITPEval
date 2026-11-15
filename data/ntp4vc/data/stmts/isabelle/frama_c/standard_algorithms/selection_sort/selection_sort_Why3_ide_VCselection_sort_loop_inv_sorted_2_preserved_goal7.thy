theory selection_sort_Why3_ide_VCselection_sort_loop_inv_sorted_2_preserved_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal7:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i_2; a_3 :: addr = shift a i_3; a_4 :: addr = shift a i_1; a_5 :: int = a_2 a_3; a_6 :: addr \<Rightarrow> int = a_2(a_4 := a_5, a_3 := i); a_7 :: int = a_6 a_3; a_8 :: int = a_2 a_4; x :: int = (1 :: int) + i_3; x_2 :: int = i_1 - i_3; x_3 :: int = i_2 - i_3; a_9 :: int = a_2 (shift a (i_3 - (1 :: int))) in a_7 = a_8 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i_2 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_3 \<le> (4294967294 :: int) \<longrightarrow> i_1 \<le> (4294967295 :: int) \<longrightarrow> i_2 \<le> (4294967295 :: int) + i_3 \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 x_2 \<longrightarrow> is_sint32 (t_2 (shift a (-(1 :: int)))) \<longrightarrow> valid_rw t a_1 i_2 \<longrightarrow> valid_rd t a_3 x_3 \<longrightarrow> is_sint32 a_8 \<longrightarrow> is_sint32 a_5 \<longrightarrow> is_sint32 a_9 \<longrightarrow> p_sorted_1' a_2 a (0 :: int) i_3 \<longrightarrow> is_sint32 a_7 \<longrightarrow> p_multisetunchanged_1' a_2 t_2 a (0 :: int) i_2 \<longrightarrow> p_minelement a_2 a_3 x_3 x_2 \<longrightarrow> p_strictlowerbound_1' a_2 a_3 (0 :: int) x_2 a_8 \<longrightarrow> p_unchanged_1' a_6 a_2 a (0 :: int) i_3 \<longrightarrow> p_unchanged_1' a_6 a_2 a ((1 :: int) + i_1) i_2 \<longrightarrow> p_unchanged_1' a_6 a_2 a x i_1 \<longrightarrow> ((0 :: int) < i_3 \<longrightarrow> p_lowerbound_1' a_2 a i_3 i_2 a_9) \<longrightarrow> p_lowerbound_1' a_6 a x i_2 a_7"
  sorry
end
