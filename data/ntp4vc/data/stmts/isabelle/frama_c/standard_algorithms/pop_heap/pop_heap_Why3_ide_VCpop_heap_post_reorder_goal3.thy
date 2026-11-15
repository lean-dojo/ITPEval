theory pop_heap_Why3_ide_VCpop_heap_post_reorder_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal3:
  fixes a :: "addr"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes p :: "bool"
  fixes p_1 :: "bool"
  fixes t_1 :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); x :: int = t_4 a_1; x_1 :: int = i - (1 :: int); a_2 :: addr = shift a x_1; a_3 :: addr = shift a (to_uint32 x_1); a_4 :: addr = shift a i_1; x_2 :: int = t_3 a_2; a_5 :: addr = shift a i_3 in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> p_isheap t_4 a i \<longrightarrow> is_sint32 x \<longrightarrow> valid_rw t a_1 i \<longrightarrow> is_sint32 (t_5 a_2) \<longrightarrow> (if (2 :: int) \<le> i then valid_rd t a_1 (1 :: int) \<and> valid_rd t a_3 (1 :: int) \<and> (if t_4 a_2 < x then p = False \<and> p_1 = False \<and> t_1 = t \<and> havoc t_2 t_4 a_1 x_1 = t_3 \<and> t_3(a_2 := x, a_4 := x_2) = t_5 \<and> (0 :: int) < i_2 \<and> (0 :: int) \<le> i_1 \<and> i_1 < i_3 \<and> x_2 < t_3 (shift a (l_heapparent i_1)) \<and> (2 :: int) + i_1 \<le> i \<and> p_isheap t_3 a i \<and> p_heapmaximumchild t_3 a i i_1 i_3 \<and> p_heapmaximumchild t_4 a i (0 :: int) i_2 \<and> valid_rw t_1 a_1 i \<and> valid_rw t_1 a_4 (1 :: int) \<and> p_upperbound_1' t_3 a (0 :: int) i x \<and> valid_rd t_1 a_3 (1 :: int) \<and> valid_rw t_1 a_3 (1 :: int) \<and> ((2 :: int) + i_2 \<le> i \<longrightarrow> l_heapparent i_2 = (0 :: int)) \<and> ((2 :: int) + i_3 \<le> i \<longrightarrow> l_heapparent i_3 = i_1) \<and> (i \<le> (1 :: int) + i_3 \<or> t_3 a_5 \<le> x_2 \<and> valid_rd t_1 a_5 (1 :: int)) else t_5 = t_4) else t_5 = t_4) \<longrightarrow> p_multisetunchanged_1' t_5 t_4 a (0 :: int) i"
  sorry
end
