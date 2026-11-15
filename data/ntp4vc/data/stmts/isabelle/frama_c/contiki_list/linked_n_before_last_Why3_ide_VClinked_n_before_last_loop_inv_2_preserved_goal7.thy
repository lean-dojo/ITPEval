theory linked_n_before_last_Why3_ide_VClinked_n_before_last_loop_inv_2_preserved_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal7:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_1; x_1 :: int = i + i_2; a_3 :: addr = t_1 (shift a_2 (i + i_1)); x_3 :: int = i + i_2 - (1 :: int) in (0 :: int) < i_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 (i_2 - (1 :: int)) \<longrightarrow> is_sint32 x \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a a_2 i x a_1 \<longrightarrow> p_linked_n t t_1 (t_1 (shift a_2 x_1)) a_2 x_1 (i_1 - i_2) a_3 \<longrightarrow> p_linked_n t t_1 (t_1 (shift a_2 x_3)) a_2 x_3 ((1 :: int) + i_1 - i_2) a_3"
  sorry
end
