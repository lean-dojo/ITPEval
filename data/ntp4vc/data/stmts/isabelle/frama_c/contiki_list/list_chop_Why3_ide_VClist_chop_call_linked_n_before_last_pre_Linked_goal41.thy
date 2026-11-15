theory list_chop_Why3_ide_VClist_chop_call_linked_n_before_last_pre_Linked_goal41
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal41:
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i_1 + i_2; a_2 :: addr = t_1 (shift a_1 x); a_3 :: addr = t_1 (shift a_2 (0 :: int)); a_4 :: addr = t_1 (shift a_3 (0 :: int)); a_5 :: addr = t_1 a; a_6 :: addr = shift a_1 (0 :: int); x_1 :: int = i + i_1 in a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_4 = a_5 \<longrightarrow> \<not>a_4 = t_1 (shift a_5 (0 :: int)) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> (2 :: int) + i_2 \<le> i \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_6 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_6 (2147483646 :: int) \<longrightarrow> separated a_5 (4 :: int) a_6 (2147483646 :: int) \<longrightarrow> valid_rw t a_3 (4 :: int) \<longrightarrow> p_linked_n t t_1 a_5 a_1 i_1 i a_4 \<longrightarrow> p_linked_n t t_1 a_2 a_1 x (i - i_2) a_4 \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < x_1 \<longrightarrow> separated a (1 :: int) (t_1 (shift a_1 i_3)) (4 :: int)) \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < x_1 \<longrightarrow> separated (t_1 (shift a_1 i_3)) (4 :: int) a_6 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_4 :: int) (i_3 :: int). \<not>i_4 = i_3 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_3 < x_1 \<longrightarrow> i_4 < x_1 \<longrightarrow> \<not>t_1 (shift a_1 i_4) = t_1 (shift a_1 i_3)) \<longrightarrow> (\<forall>(i_4 :: int) (i_3 :: int). \<not>i_4 = i_3 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_3 < x_1 \<longrightarrow> i_4 < x_1 \<longrightarrow> separated (t_1 (shift a_1 i_4)) (4 :: int) (t_1 (shift a_1 i_3)) (4 :: int)) \<longrightarrow> p_linked_n t t_1 a_5 a_1 i_1 (i - (1 :: int)) (t_1 (shift a_1 (i + i_1 - (1 :: int))))"
  sorry
end
