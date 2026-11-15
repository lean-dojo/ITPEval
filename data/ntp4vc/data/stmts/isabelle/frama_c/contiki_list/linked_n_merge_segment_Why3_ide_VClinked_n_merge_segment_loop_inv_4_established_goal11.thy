theory linked_n_merge_segment_Why3_ide_VClinked_n_merge_segment_loop_inv_4_established_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal11:
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i_1 + i_2 in \<not>i_2 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t (shift a_3 (0 :: int)) (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a a_3 i_1 i_2 a_2 \<longrightarrow> p_linked_n t t_1 a_2 a_3 x i a_1 \<longrightarrow> p_linked_n t t_1 (t_1 (shift (t_1 (shift a_3 (i_1 + i_2 - (1 :: int)))) (0 :: int))) a_3 x i a_1"
  sorry
end
