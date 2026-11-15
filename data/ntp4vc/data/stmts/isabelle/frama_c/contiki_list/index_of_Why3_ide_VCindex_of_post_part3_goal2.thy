theory index_of_Why3_ide_VCindex_of_post_part3_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/A_Index_of_item_A_Index_of_item"
begin
theorem goal2:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i_1 \<le> i"
  assumes fact2: "i \<le> i_1"
  assumes fact3: "i_2 \<le> i_1"
  assumes fact4: "(0 :: int) \<le> i_2"
  assumes fact5: "i_2 < i"
  assumes fact6: "region (base a) \<le> (0 :: int)"
  assumes fact7: "region (base a_1) \<le> (0 :: int)"
  assumes fact8: "framed t_1"
  assumes fact9: "linked t"
  assumes fact10: "is_sint32 i"
  assumes fact11: "is_sint32 i_1"
  assumes fact12: "is_sint32 i_2"
  assumes fact13: "i_2 \<le> i \<longrightarrow> valid_rw t (shift a_1 i_2) (i - i_2)"
  assumes fact14: "\<forall>(i_3 :: int). i_3 < i_1 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> \<not>t_1 (shift a_1 i_3) = a"
  shows "l_index_of t_1 a a_1 i_2 i_1 = i_1"
  sorry
end
