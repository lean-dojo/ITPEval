theory linked_n_merge_segment_right_Why3_ide_VClinked_n_merge_segment_right_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "region (base a_1) \<le> (0 :: int)"
  assumes fact3: "region (base a_2) \<le> (0 :: int)"
  assumes fact4: "region (base a_3) \<le> (0 :: int)"
  assumes fact5: "framed t_1"
  assumes fact6: "linked t"
  assumes fact7: "is_sint32 i"
  assumes fact8: "is_sint32 i_1"
  assumes fact9: "valid_rw t (shift a_3 (0 :: int)) (2147483646 :: int)"
  assumes fact10: "p_linked_n t t_1 a a_3 i_1 i a_2"
  assumes fact11: "p_linked_n t t_1 a_2 a_3 (i + i_1) (1 :: int) a_1"
  shows "p_linked_n t t_1 a a_3 i_1 ((1 :: int) + i) a_1"
  sorry
end
