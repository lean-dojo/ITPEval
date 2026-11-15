theory list_pop_Why3_ide_VClist_pop_more_post_NoMoreHere_part1_goal24
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal24:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = t_1 a; x :: int = i + i_1; a_3 :: addr = shift a_1 (0 :: int) in \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> (2 :: int) + i_2 \<le> x \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_3 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_3 (2147483646 :: int) \<longrightarrow> separated a_2 (4 :: int) a_3 (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a_2 a_1 i_1 i (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < x \<longrightarrow> separated a (1 :: int) (t_1 (shift a_1 i_3)) (4 :: int)) \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < x \<longrightarrow> separated (t_1 (shift a_1 i_3)) (4 :: int) a_3 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_4 :: int) (i_3 :: int). \<not>i_4 = i_3 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_3 < x \<longrightarrow> i_4 < x \<longrightarrow> \<not>t_1 (shift a_1 i_4) = t_1 (shift a_1 i_3)) \<longrightarrow> (\<forall>(i_4 :: int) (i_3 :: int). \<not>i_4 = i_3 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_3 < x \<longrightarrow> i_4 < x \<longrightarrow> separated (t_1 (shift a_1 i_4)) (4 :: int) (t_1 (shift a_1 i_3)) (4 :: int)) \<longrightarrow> \<not>(t_1(a := t_1 (shift a_2 (0 :: int)))) (shift a_1 i_2) = a_2"
  sorry
end
