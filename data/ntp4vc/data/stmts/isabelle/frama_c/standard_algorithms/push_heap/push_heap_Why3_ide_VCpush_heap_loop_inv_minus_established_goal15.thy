theory push_heap_Why3_ide_VCpush_heap_loop_inv_minus_established_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal15:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i - (1 :: int); x_1 :: int = l_heapparent x; a_1 :: addr = shift a x_1; x_2 :: int = t_1 a_1; a_2 :: addr = shift a x; x_3 :: int = t_1 a_2; a_3 :: addr = shift a (to_uint32 x); m :: addr \<Rightarrow> int = t_1(a_2 := x_2) in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) < x_1 \<longrightarrow> x_2 < x_3 \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_isheap t_1 a x \<longrightarrow> is_uint32 (l_heapparent x_1) \<longrightarrow> is_sint32 x_3 \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> is_sint32 (m a_1) \<longrightarrow> p_multisetminus m t_1 a i x_3"
  sorry
end
