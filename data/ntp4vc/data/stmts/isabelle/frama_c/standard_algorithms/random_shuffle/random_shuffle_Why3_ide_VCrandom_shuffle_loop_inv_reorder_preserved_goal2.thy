theory random_shuffle_Why3_ide_VCrandom_shuffle_loop_inv_reorder_preserved_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal2:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i_2; a_3 :: addr = shift a i_3; a_4 :: addr = shift a (to_uint32 ((1 :: int) + i_1)); a_5 :: int = a_2 a_3; a_6 :: addr \<Rightarrow> int = a_2(a_4 := a_5, a_3 := i); a_7 :: int = a_6 a_3; a_8 :: int = a_2 a_4 in a_7 = a_8 \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> (0 :: int) < i_3 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i_3 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> i_3 < i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> valid_rw t a_1 i_2 \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> is_sint32 a_5 \<longrightarrow> is_sint32 a_8 \<longrightarrow> valid_rw t a_4 (1 :: int) \<longrightarrow> is_sint32 a_7 \<longrightarrow> p_unchanged_1' a_2 t_2 a i_3 i_2 \<longrightarrow> p_multisetunchanged_1' a_2 t_2 a (0 :: int) i_3 \<longrightarrow> p_multisetunchanged_1' a_6 t_2 a (0 :: int) (to_uint32 ((1 :: int) + i_3))"
  sorry
end
