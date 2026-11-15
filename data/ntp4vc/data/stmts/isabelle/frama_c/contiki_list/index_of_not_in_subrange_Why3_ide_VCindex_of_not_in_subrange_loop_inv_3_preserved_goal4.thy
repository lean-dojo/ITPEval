theory index_of_not_in_subrange_Why3_ide_VCindex_of_not_in_subrange_loop_inv_3_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/A_Index_of_item_A_Index_of_item"
begin
theorem goal4:
  fixes i_2 :: "int"
  fixes t :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  shows "let x :: int = (1 :: int) + i_2; x_1 :: int = l_index_of t a a_1 i_4 i in \<not>t (shift a_1 i_2) = a \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_4 \<le> i_1 \<longrightarrow> i_2 < i_1 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> i_4 \<le> i_2 \<longrightarrow> i_4 \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 i_4 \<longrightarrow> is_sint32 x \<longrightarrow> (\<forall>(i_5 :: int). i_5 < i_1 \<longrightarrow> i_4 \<le> i_5 \<longrightarrow> \<not>t (shift a_1 i_5) = a) \<longrightarrow> (\<forall>(i_5 :: int). i_5 < i_2 \<longrightarrow> i_4 \<le> i_5 \<longrightarrow> x_1 = l_index_of t a a_1 i_2 i) \<longrightarrow> l_index_of t a a_1 x i = x_1"
  sorry
end
