theory array_push_Why3_ide_VCarray_push_loop_inv_LeftLinked_preserved_part2_goal24
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1"
begin
theorem goal24:
  fixes i_3 :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes a_4 :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> real"
  shows "let x :: int = (1 :: int) + i_3; a_5 :: addr \<Rightarrow> addr = havoc t_2 t_3 (shift a_4 ((1 :: int) + i_2)) i_1; a_6 :: addr = t_3 a_1; x_1 :: int = i_1 + i_2; x_2 :: int = i_2 + i_3; x_3 :: int = (1 :: int) + i_2 + i_3; a_7 :: addr = shift a_4 (0 :: int); x_4 :: int = (2 :: int) + i_2 + i_3; a_8 :: addr = a_5 (shift a_4 x_2) in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> (x = i_1 \<longleftrightarrow> i = (0 :: int)) \<longrightarrow> ((2 :: int) + i_3 \<le> i_1 \<longleftrightarrow> i = (1 :: int)) \<longrightarrow> a_5 a_1 = a_6 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i_3 \<longrightarrow> x_1 \<le> (2147483645 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint32 x_1 \<longrightarrow> is_sint32 x_2 \<longrightarrow> is_sint32 x_3 \<longrightarrow> valid_rw t a_7 (2147483646 :: int) \<longrightarrow> separated a_1 (1 :: int) a_7 (2147483646 :: int) \<longrightarrow> separated a_6 (4 :: int) a_7 (2147483646 :: int) \<longrightarrow> p_linked_n t t_3 a a_4 i_2 i_1 a_3 \<longrightarrow> p_array_swipe_right a_5 t_3 a_4 x_4 ((1 :: int) + i_1 + i_2) \<longrightarrow> p_linked_n t a_5 a a_4 i_2 x a_2 \<longrightarrow> p_linked_n t a_5 a_2 a_4 x_4 (i_1 - (1 :: int) - i_3) a_3 \<longrightarrow> p_unchanged t a_5 t_1 t t_3 t_1 a_4 i_2 x_3 \<longrightarrow> (\<forall>(i_4 :: int). i_2 \<le> i_4 \<longrightarrow> i_4 < x_1 \<longrightarrow> separated a_1 (1 :: int) (t_3 (shift a_4 i_4)) (4 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). i_2 \<le> i_4 \<longrightarrow> i_4 < x_1 \<longrightarrow> separated (t_3 (shift a_4 i_4)) (4 :: int) a_7 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_2 \<le> i_4 \<longrightarrow> i_2 \<le> i_5 \<longrightarrow> i_4 < x_1 \<longrightarrow> i_5 < x_1 \<longrightarrow> \<not>t_3 (shift a_4 i_5) = t_3 (shift a_4 i_4)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_2 \<le> i_4 \<longrightarrow> i_2 \<le> i_5 \<longrightarrow> i_4 < x_1 \<longrightarrow> i_5 < x_1 \<longrightarrow> separated (t_3 (shift a_4 i_5)) (4 :: int) (t_3 (shift a_4 i_4)) (4 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). i_4 \<le> x_1 \<longrightarrow> x_4 \<le> i_4 \<longrightarrow> separated a_1 (1 :: int) (a_5 (shift a_4 i_4)) (4 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). i_2 \<le> i_4 \<longrightarrow> i_4 < i + i_1 + i_2 \<longrightarrow> separated (a_5 (shift a_4 i_4)) (4 :: int) a_7 (2147483646 :: int)) \<longrightarrow> p_linked_n t (a_5(shift a_4 x_3 := a_8)) a a_4 i_2 i_3 a_8"
  sorry
end
