theory list_final_add_Why3_ide_VClist_final_add_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_3 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_4 :: addr = t_1 (shift a_1 (0 :: int)); x :: int = i + i_1; a_5 :: addr = shift a_3 (0 :: int); a_6 :: addr = t_1 a; a_7 :: addr = shift a_2 (0 :: int); m :: addr \<Rightarrow> addr = t_1(a_7 := a_1, shift a_3 x := a_1) in a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> x \<le> (2147483645 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (4 :: int) \<longrightarrow> valid_rw t a_2 (4 :: int) \<longrightarrow> separated a (1 :: int) a_1 (4 :: int) \<longrightarrow> separated a (1 :: int) a_2 (4 :: int) \<longrightarrow> separated a_2 (4 :: int) a_1 (4 :: int) \<longrightarrow> valid_rw t a_5 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_5 (2147483646 :: int) \<longrightarrow> separated a_1 (4 :: int) a_5 (2147483646 :: int) \<longrightarrow> separated a_6 (4 :: int) a_5 (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a_6 a_3 i_1 (i - (1 :: int)) a_2 \<longrightarrow> p_linked_n t t_1 a_2 a_3 (i + i_1 - (1 :: int)) (1 :: int) (t_1 a_7) \<longrightarrow> (\<forall>(i_2 :: int). i_1 \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> separated a (1 :: int) (t_1 (shift a_3 i_2)) (4 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). i_1 \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> separated a_1 (4 :: int) (t_1 (shift a_3 i_2)) (4 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). i_1 \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> separated (t_1 (shift a_3 i_2)) (4 :: int) a_5 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_3 :: int) (i_2 :: int). \<not>i_3 = i_2 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_2 < x \<longrightarrow> i_3 < x \<longrightarrow> \<not>t_1 (shift a_3 i_3) = t_1 (shift a_3 i_2)) \<longrightarrow> (\<forall>(i_3 :: int) (i_2 :: int). \<not>i_3 = i_2 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_2 < x \<longrightarrow> i_3 < x \<longrightarrow> separated (t_1 (shift a_3 i_3)) (4 :: int) (t_1 (shift a_3 i_2)) (4 :: int)) \<longrightarrow> p_linked_n t m (m a) a_3 i_1 ((1 :: int) + i) a_4"
  sorry
end
