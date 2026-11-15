theory partial_sort_Why3_ide_VCpartial_sort_stmt_post_goal25
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal25:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_4 a_1 i_1; a_3 :: addr \<Rightarrow> int = havoc t_2 a_2 a_1 i; a_4 :: addr \<Rightarrow> int = havoc t_3 a_3 a_1 i_1; x :: int = i_1 - (1 :: int); a_5 :: int = a_4 (shift a x); a_6 :: int = a_3 a_1; a_7 :: addr = shift a i_2; a_8 :: int = a_3 a_7 in a_5 = a_6 \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> a_8 < a_6 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_7 (1 :: int) \<longrightarrow> valid_rw t a_1 i \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> p_isheap a_2 a i_1 \<longrightarrow> p_multisetunchanged_1' a_2 t_4 a (0 :: int) i_1 \<longrightarrow> is_sint32 a_6 \<longrightarrow> is_sint32 a_8 \<longrightarrow> p_isheap a_3 a i_1 \<longrightarrow> p_multisetunchanged_1' a_3 t_4 a (0 :: int) i_2 \<longrightarrow> p_unchanged_1' a_3 t_4 a i_2 i \<longrightarrow> p_upperbound_1' a_3 a (0 :: int) i_1 a_6 \<longrightarrow> p_lowerbound_1' a_3 a i_1 i_2 a_6 \<longrightarrow> is_sint32 a_5 \<longrightarrow> p_isheap a_4 a x \<longrightarrow> p_multisetunchanged_1' a_4 a_3 a (0 :: int) i_1 \<longrightarrow> p_maxelement a_4 a i_1 x \<longrightarrow> p_multisetunchanged_1' a_4 t_4 a (0 :: int) ((1 :: int) + i_2)"
  sorry
end
