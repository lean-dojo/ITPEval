theory partial_sort_Why3_ide_VCpartial_sort_loop_inv_upper_established_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count"
begin
theorem goal10:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i_1; a_3 :: int = a_2 a_1 in (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_1 i \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> is_sint32 a_3 \<longrightarrow> p_isheap a_2 a i_1 \<longrightarrow> p_multisetunchanged_1' a_2 t_2 a (0 :: int) i_1 \<longrightarrow> p_upperbound_1' a_2 a (0 :: int) i_1 a_3"
  sorry
end
