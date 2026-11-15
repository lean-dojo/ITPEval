theory index_of_Why3_ide_VCindex_of_post_part2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/A_Index_of_item_A_Index_of_item"
begin
theorem goal1:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = t_1 (shift a i_1) in (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> (i_2 \<le> i \<longrightarrow> valid_rw t (shift a i_2) (i - i_2)) \<longrightarrow> (\<forall>(i_3 :: int). i_3 < i_1 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> \<not>a_1 = t_1 (shift a i_3)) \<longrightarrow> l_index_of t_1 a_1 a i_2 i = i_1"
  sorry
end
