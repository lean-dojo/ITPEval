theory sort_heap_Why3_ide_VCsort_heap_loop_inv_reorder_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal6:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_3 a_1 i; a_3 :: addr \<Rightarrow> int = havoc t_2 a_2 a_1 i_1; x :: int = i_1 - (1 :: int); a_4 :: int = a_3 (shift a x); a_5 :: int = a_2 a_1 in a_4 = a_5 \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_isheap t_3 a i \<longrightarrow> is_sint32 (t_3 a_1) \<longrightarrow> valid_rw t a_1 i \<longrightarrow> is_sint32 a_5 \<longrightarrow> p_isheap a_2 a i_1 \<longrightarrow> p_sorted_1' a_2 a i_1 i \<longrightarrow> p_multisetunchanged_1' a_2 t_3 a (0 :: int) i \<longrightarrow> p_lowerbound_1' a_2 a i_1 i a_5 \<longrightarrow> is_sint32 (a_3 a_1) \<longrightarrow> is_sint32 a_4 \<longrightarrow> p_isheap a_3 a x \<longrightarrow> p_maxelement a_3 a i_1 x \<longrightarrow> p_unchanged_1' a_3 a_2 a i_1 i \<longrightarrow> p_multisetunchanged_1' a_3 a_2 a (0 :: int) i_1 \<longrightarrow> p_multisetunchanged_1' a_3 t_3 a (0 :: int) i"
  sorry
end
