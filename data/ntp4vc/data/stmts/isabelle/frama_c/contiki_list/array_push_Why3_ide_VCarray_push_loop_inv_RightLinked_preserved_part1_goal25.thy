theory array_push_Why3_ide_VCarray_push_loop_inv_RightLinked_preserved_part1_goal25
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1"
begin
theorem goal25:
  fixes a_4 :: "addr"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> real"
  shows "let a_5 :: addr = shift a_4 i_1; x :: int = (1 :: int) + i_2; a_6 :: addr \<Rightarrow> addr = havoc t_2 t_3 a_5 x; a_7 :: addr = t_3 a; x_1 :: int = i_1 + i_2; x_2 :: int = i_1 - (1 :: int); a_8 :: addr = shift a_4 (0 :: int); x_3 :: int = (1 :: int) + i_1 in \<not>i_2 = -(1 :: int) \<longrightarrow> (i_2 = (0 :: int) \<longleftrightarrow> i = (0 :: int)) \<longrightarrow> ((0 :: int) < i_2 \<longleftrightarrow> i = (1 :: int)) \<longrightarrow> a_6 a = a_7 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> x_1 \<le> (2147483645 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> is_sint32 x_2 \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rw t a_8 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_8 (2147483646 :: int) \<longrightarrow> separated a_7 (4 :: int) a_8 (2147483646 :: int) \<longrightarrow> p_linked_n t t_3 a_2 a_4 x_2 x a_3 \<longrightarrow> p_array_swipe_right a_6 t_3 a_4 x_3 ((1 :: int) + i_1 + i_2) \<longrightarrow> p_linked_n t a_6 a_1 a_4 x_3 i_2 a_3 \<longrightarrow> p_linked_n t a_6 a_2 a_4 x_2 (1 :: int) a_1 \<longrightarrow> p_unchanged t a_6 t_1 t t_3 t_1 a_4 x_2 i_1 \<longrightarrow> (\<forall>(i_3 :: int). i_3 < x_1 \<longrightarrow> i_1 \<le> (1 :: int) + i_3 \<longrightarrow> separated a (1 :: int) (t_3 (shift a_4 i_3)) (4 :: int)) \<longrightarrow> (\<forall>(i_3 :: int). i_3 < x_1 \<longrightarrow> i_1 \<le> (1 :: int) + i_3 \<longrightarrow> separated (t_3 (shift a_4 i_3)) (4 :: int) a_8 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_4 :: int) (i_3 :: int). \<not>i_4 = i_3 \<longrightarrow> i_3 < x_1 \<longrightarrow> i_4 < x_1 \<longrightarrow> i_1 \<le> (1 :: int) + i_3 \<longrightarrow> i_1 \<le> (1 :: int) + i_4 \<longrightarrow> \<not>t_3 (shift a_4 i_4) = t_3 (shift a_4 i_3)) \<longrightarrow> (\<forall>(i_3 :: int). i_1 < i_3 \<longrightarrow> i_3 \<le> x_1 \<longrightarrow> separated a (1 :: int) (a_6 (shift a_4 i_3)) (4 :: int)) \<longrightarrow> (\<forall>(i_3 :: int). i_3 < i + i_1 + i_2 \<longrightarrow> i_1 \<le> (1 :: int) + i_3 \<longrightarrow> separated (a_6 (shift a_4 i_3)) (4 :: int) a_8 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_4 :: int) (i_3 :: int). \<not>i_4 = i_3 \<longrightarrow> i_3 < x_1 \<longrightarrow> i_4 < x_1 \<longrightarrow> i_1 \<le> (1 :: int) + i_3 \<longrightarrow> i_1 \<le> (1 :: int) + i_4 \<longrightarrow> separated (t_3 (shift a_4 i_4)) (4 :: int) (t_3 (shift a_4 i_3)) (4 :: int)) \<longrightarrow> p_linked_n t (a_6(a_5 := a_6 (shift a_4 x_2))) a_2 a_4 i_1 x a_3"
  sorry
end
