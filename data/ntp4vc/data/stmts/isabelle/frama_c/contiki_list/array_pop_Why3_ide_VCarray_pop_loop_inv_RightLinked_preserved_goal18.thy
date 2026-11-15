theory array_pop_Why3_ide_VCarray_pop_loop_inv_RightLinked_preserved_goal18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Axiomatic1_Axiomatic1"
begin
theorem goal18:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes a_4 :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> real"
  shows "let a_5 :: addr \<Rightarrow> addr = havoc t_2 t_3 (shift a_4 i_2) (i - (1 :: int)); a_6 :: addr = t_3 a_1; x :: int = i + i_2; x_1 :: int = (2 :: int) + i_3; x_2 :: int = (1 :: int) + i_3; a_7 :: addr = shift a_4 (0 :: int); a_8 :: addr = t_3 (shift a_4 i_1); x_3 :: int = i_2 - i_1; a_9 :: addr \<Rightarrow> addr = a_5(shift a_4 i_3 := a_5 (shift a_4 x_2)) in a_5 a_1 = a_6 \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> i_3 < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rw t a_7 (2147483646 :: int) \<longrightarrow> separated a_1 (1 :: int) a_7 (2147483646 :: int) \<longrightarrow> separated a_6 (4 :: int) a_7 (2147483646 :: int) \<longrightarrow> p_linked_n t t_3 a a_4 i_2 i a_3 \<longrightarrow> p_linked_n t t_3 a_8 a_4 i_1 x_3 a \<longrightarrow> p_array_swipe_left a_5 t_3 a_4 i_2 i_3 \<longrightarrow> p_linked_n t a_5 a_2 a_4 x_2 (i + i_2 - (1 :: int) - i_3) a_3 \<longrightarrow> p_linked_n t a_5 a_8 a_4 i_1 x_3 a \<longrightarrow> p_linked_n t a_5 (a_5 (shift a (0 :: int))) a_4 i_2 (i_3 - i_2) a_2 \<longrightarrow> p_unchanged t a_5 t_1 t t_3 t_1 a_4 i_1 i_2 \<longrightarrow> p_unchanged t a_5 t_1 t t_3 t_1 a_4 i_3 x \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> separated a_1 (1 :: int) (t_3 (shift a_4 i_4)) (4 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> separated (t_3 (shift a_4 i_4)) (4 :: int) a_7 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> i_4 < x \<longrightarrow> i_5 < x \<longrightarrow> \<not>t_3 (shift a_4 i_5) = t_3 (shift a_4 i_4)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> i_4 < x \<longrightarrow> i_5 < x \<longrightarrow> separated (t_3 (shift a_4 i_5)) (4 :: int) (t_3 (shift a_4 i_4)) (4 :: int)) \<longrightarrow> p_linked_n t a_9 (a_9 (shift a_2 (0 :: int))) a_4 x_1 (i + i_2 - (2 :: int) - i_3) a_3"
  sorry
end
