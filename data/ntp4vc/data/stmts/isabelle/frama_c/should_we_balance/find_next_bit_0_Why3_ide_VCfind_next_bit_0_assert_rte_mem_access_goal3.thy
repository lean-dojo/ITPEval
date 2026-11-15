theory find_next_bit_0_Why3_ide_VCfind_next_bit_0_assert_rte_mem_access_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_2 in i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint8 (t_1 a_1) \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> t_1 (shift a i_3) = (0 :: int)) \<longrightarrow> valid_rd t a_1 (1 :: int)"
  sorry
end
