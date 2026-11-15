theory make_heap_Why3_ide_VCmake_heap_loop_inv_reorder_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal3:
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_1; a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_3 a_1 i; a_3 :: addr \<Rightarrow> int = havoc t_2 a_2 a_1 x in (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> valid_rw t a_1 i \<longrightarrow> valid_rw t a_1 x \<longrightarrow> p_isheap a_2 a i_1 \<longrightarrow> p_multisetunchanged_1' a_2 t_3 a (0 :: int) x \<longrightarrow> p_unchanged_1' a_2 t_3 a x i \<longrightarrow> p_isheap a_3 a x \<longrightarrow> p_multisetunchanged_1' a_3 a_2 a (0 :: int) x \<longrightarrow> p_multisetunchanged_1' a_3 t_3 a (0 :: int) ((2 :: int) + i_1)"
  sorry
end
