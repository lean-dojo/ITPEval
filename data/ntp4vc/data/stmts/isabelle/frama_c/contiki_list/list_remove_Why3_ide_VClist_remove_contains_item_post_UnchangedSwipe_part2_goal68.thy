theory list_remove_Why3_ide_VClist_remove_contains_item_post_UnchangedSwipe_part2_goal68
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/A_Index_of_item_A_Index_of_item"
begin
theorem goal68:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> real"
  shows "let a_2 :: addr = t_2 a; a_3 :: addr = t_2 (shift a_1 i_2); x :: int = i + i_1; x_1 :: int = l_index_of t_2 a_3 a_1 i_1 x; a_4 :: addr = shift a_1 (0 :: int); m :: addr \<Rightarrow> addr = t_2(a := t_2 (shift a_2 (0 :: int))) in \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> a_3 = a_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_1 \<le> i_3 \<longrightarrow> i \<le> (2147483645 :: int) \<longrightarrow> (2 :: int) + i_3 \<le> x \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_4 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_4 (2147483646 :: int) \<longrightarrow> separated a_2 (4 :: int) a_4 (2147483646 :: int) \<longrightarrow> p_linked_n t t_2 a_2 a_1 i_1 i (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> is_sint32 x_1 \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> separated a (1 :: int) (t_2 (shift a_1 i_4)) (4 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> separated (t_2 (shift a_1 i_4)) (4 :: int) a_4 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). let a_5 :: addr = t_2 (shift a_1 i_4) in \<not>a_3 = a_5 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> separated a_3 (4 :: int) a_5 (4 :: int)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> i_4 < x \<longrightarrow> i_5 < x \<longrightarrow> \<not>t_2 (shift a_1 i_5) = t_2 (shift a_1 i_4)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> i_4 < x \<longrightarrow> i_5 < x \<longrightarrow> separated (t_2 (shift a_1 i_5)) (4 :: int) (t_2 (shift a_1 i_4)) (4 :: int)) \<longrightarrow> eqs1_list (load_s1_list (m (shift a_1 i_3)) t_1 m) (load_s1_list (t_2 (shift a_1 ((1 :: int) + i_3))) t_1 t_2)"
  sorry
end
