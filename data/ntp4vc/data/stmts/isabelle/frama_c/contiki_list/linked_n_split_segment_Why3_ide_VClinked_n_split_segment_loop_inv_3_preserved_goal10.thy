theory linked_n_split_segment_Why3_ide_VClinked_n_split_segment_loop_inv_3_preserved_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal10:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a_2 :: "addr"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i + i_1; x_1 :: int = i_3 - (1 :: int); a_3 :: addr = t_1 (shift (t_1 (shift a_2 (i_2 + i_3 - (1 :: int)))) (0 :: int)) in (0 :: int) < i \<longrightarrow> i < i_3 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i \<le> i_3 \<longrightarrow> i_3 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base (t_1 (shift (t_1 (shift a_2 (i + i_2 - (1 :: int)))) (0 :: int)))) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 x_1 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a a_2 i_2 x a_1 \<longrightarrow> p_linked_n t t_1 a a_2 i_2 i_3 a_3 \<longrightarrow> p_linked_n t t_1 a_3 a_2 (i_2 + i_3) (i + i_1 - i_3) a_1 \<longrightarrow> p_linked_n t t_1 a a_2 i_2 x_1 (t_1 (shift (t_1 (shift a_2 (i_2 + i_3 - (2 :: int)))) (0 :: int)))"
  sorry
end
