theory index_of_up_unexisting_item_Why3_ide_VCindex_of_up_unexisting_item_loop_inv_3_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Index_of_item_A_Index_of_item" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes i_1 :: "int"
  fixes t :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  shows "let x :: int = (1 :: int) + i_1 in l_index_of t a a_1 i_3 i = i \<longrightarrow> i_1 \<le> i \<longrightarrow> i_3 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 x \<longrightarrow> (\<forall>(i_4 :: int). i_4 < i_1 \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> \<not>t (shift a_1 i_4) = a) \<longrightarrow> (\<forall>(i_4 :: int). i_4 < i_1 \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> l_index_of t a a_1 i_1 i = i) \<longrightarrow> l_index_of t a a_1 x i = i"
  sorry
end
