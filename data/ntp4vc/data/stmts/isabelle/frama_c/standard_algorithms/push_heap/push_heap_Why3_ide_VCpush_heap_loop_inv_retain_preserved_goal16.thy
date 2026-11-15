theory push_heap_Why3_ide_VCpush_heap_loop_inv_retain_preserved_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal16:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i - (1 :: int); x_1 :: int = l_heapparent x; a_1 :: addr = shift a x_1; x_2 :: int = t_2 a_1; a_2 :: addr = shift a x; x_3 :: int = t_2 a_2; m :: addr \<Rightarrow> int = t_2(a_2 := x_2); a_3 :: addr = shift a (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 m a_3 i; a_5 :: addr = shift a i_1; a_6 :: int = a_4 a_5; x_4 :: int = l_heapparent i_1; a_7 :: addr = shift a x_4; a_8 :: int = a_4 a_7; x_5 :: int = t_3 a_7; a_9 :: addr = shift a (to_uint32 x) in (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) < x_1 \<longrightarrow> x_2 < x_3 \<longrightarrow> a_6 < x_3 \<longrightarrow> a_8 < x_3 \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> (2 :: int) + i_1 \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x_4 \<longrightarrow> valid_rd t a_5 (1 :: int) \<longrightarrow> valid_rw t a_3 i \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_isheap t_2 a x \<longrightarrow> is_sint32 x_5 \<longrightarrow> valid_rd t a_7 (1 :: int) \<longrightarrow> is_uint32 (l_heapparent x_1) \<longrightarrow> is_sint32 x_3 \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t a_9 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_9 (1 :: int) \<longrightarrow> is_sint32 (m a_1) \<longrightarrow> is_sint32 a_6 \<longrightarrow> is_sint32 a_8 \<longrightarrow> p_isheap a_4 a i \<longrightarrow> p_multisetminus a_4 t_2 a i x_3 \<longrightarrow> p_multisetadd a_4 t_2 a i a_6 \<longrightarrow> p_multisetretainrest_3' a_4 t_2 a i x_3 a_6 \<longrightarrow> (if a_6 < a_8 then a_4(a_5 := a_8) = t_3 \<and> valid_rw t a_5 (1 :: int) else a_4 = t_3) \<longrightarrow> p_multisetretainrest_3' t_3 t_2 a i x_3 x_5"
  sorry
end
