theory linked_n_split_segment_Why3_ide_VClinked_n_split_segment_loop_inv_3_established_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal11:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i + i_1 in (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base (t_1 (shift (t_1 (shift a_2 (i + i_2 - (1 :: int)))) (0 :: int)))) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a a_2 i_2 x a_1 \<longrightarrow> p_linked_n t t_1 a a_2 i_2 x (t_1 (shift (t_1 (shift a_2 (i + i_1 + i_2 - (1 :: int)))) (0 :: int)))"
  sorry
end
