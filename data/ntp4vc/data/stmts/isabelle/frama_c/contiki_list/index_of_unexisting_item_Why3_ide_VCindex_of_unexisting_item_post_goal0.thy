theory index_of_unexisting_item_Why3_ide_VCindex_of_unexisting_item_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/A_Index_of_item_A_Index_of_item"
begin
theorem goal0:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "addr \<Rightarrow> addr"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "(0 :: int) \<le> i_1"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "region (base a_1) \<le> (0 :: int)"
  assumes fact4: "framed t"
  assumes fact5: "is_sint32 i"
  assumes fact6: "is_sint32 i_1"
  assumes fact7: "\<forall>(i_2 :: int). i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> \<not>t (shift a_1 i_2) = a"
  shows "l_index_of t a a_1 i_1 i = i"
  sorry
end
