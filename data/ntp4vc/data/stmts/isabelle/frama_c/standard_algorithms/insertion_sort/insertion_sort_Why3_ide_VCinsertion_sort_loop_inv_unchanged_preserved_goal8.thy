theory insertion_sort_Why3_ide_VCinsertion_sort_loop_inv_unchanged_preserved_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal8:
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x_1 :: int = i_2 - i_1; x_2 :: int = (1 :: int) + i_2; a_1 :: addr = shift a (0 :: int); a_2 :: addr = shift a i_2; a_3 :: addr = shift a i_1; x_3 :: int = (1 :: int) + i_2 - i_1; a_4 :: addr \<Rightarrow> int = havoc t_1 t_3 a_1 i; a_5 :: int = a_4 a_2; a_6 :: addr \<Rightarrow> int = havoc t_2 a_4 a_3 x_3 in i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> i_2 \<le> (4294967295 :: int) + i_1 \<longrightarrow> to_uint32 x_1 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 x_2 \<longrightarrow> valid_rd t a_1 i_2 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rw t a_1 i \<longrightarrow> valid_rw t a_3 x_3 \<longrightarrow> is_sint32 a_5 \<longrightarrow> p_sorted_1' a_4 a (0 :: int) i_2 \<longrightarrow> p_unchanged_1' a_4 t_3 a i_2 i \<longrightarrow> p_multisetunchanged_1' a_4 t_3 a (0 :: int) i_2 \<longrightarrow> p_upperbound_1' a_4 a (0 :: int) i_1 a_5 \<longrightarrow> p_strictlowerbound_1' a_4 a i_1 i_2 a_5 \<longrightarrow> p_equalranges_4' a_6 a_4 a_3 (0 :: int) x_1 (1 :: int) \<longrightarrow> p_equalranges_4' a_6 a_4 a_3 x_1 x_3 (0 :: int) \<longrightarrow> p_unchanged_1' a_6 t_3 a x_2 i"
  sorry
end
