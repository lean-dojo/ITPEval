theory push_heap_Why3_ide_VCpush_heap_post_reorder_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal1:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_5 :: "int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes p_1 :: "bool"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes p :: "bool"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); x :: int = i_1 - (1 :: int); a_2 :: addr = shift a i_5; a_3 :: addr = shift a (to_uint32 x); x_1 :: int = t_4 a_2; a_4 :: addr = shift a x; x_2 :: int = t_4 a_4; a_5 :: addr = shift a i_3; m :: addr \<Rightarrow> int = t_4(a_4 := x_1); x_3 :: int = t_2 a_5; a_6 :: addr = shift a i in (0 :: int) < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> p_isheap t_4 a x \<longrightarrow> (if (2 :: int) \<le> i_1 then p_1 = False \<and> l_heapparent x = i_5 \<and> valid_rd t a_2 (1 :: int) \<and> valid_rd t a_3 (1 :: int) \<and> (if x_1 < x_2 then t_2(a_5 := x_2) = t_3 \<and> valid_rw t a_5 (1 :: int) \<and> valid_rw t a_3 (1 :: int) \<and> (if (0 :: int) < i_5 then p = False \<and> i_3 = i_2 \<and> i_4 = i_2 \<and> i_4 = i_3 \<and> l_heapparent i_3 = i \<and> havoc t_1 m a_1 i_1 = t_2 \<and> (0 :: int) \<le> i_3 \<and> x_3 < x_2 \<and> (2 :: int) + i_3 \<le> i_1 \<and> p_isheap t_2 a i_1 \<and> p_multisetadd t_2 t_4 a i_1 x_3 \<and> p_multisetminus t_2 t_4 a i_1 x_2 \<and> p_multisetretainrest_3' t_2 t_4 a i_1 x_2 x_3 \<and> (i_3 \<le> (0 :: int) \<or> x_2 \<le> t_2 a_6 \<and> valid_rd t a_6 (1 :: int)) else i_5 = i_3 \<and> m = t_2) else t_4 = t_3) else t_4 = t_3) \<longrightarrow> p_multisetunchanged_1' t_3 t_4 a (0 :: int) i_1"
  sorry
end
