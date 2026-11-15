theory list_copy_Why3_ide_VClist_copy_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let a_3 :: addr = shift a_2 (0 :: int); a_4 :: addr = t_1 a in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t a_3 (2147483646 :: int) \<longrightarrow> separated a_1 (1 :: int) a_3 (2147483646 :: int) \<longrightarrow> separated (t_1 a_1) (4 :: int) a_3 (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a_4 a_2 i_1 i (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). i_1 \<le> i_2 \<longrightarrow> i_2 < i + i_1 \<longrightarrow> separated a_1 (1 :: int) (t_1 (shift a_2 i_2)) (4 :: int)) \<longrightarrow> p_linked_n t (t_1(a_1 := a_4)) a_4 a_2 i_1 i (Mk_addr (0 :: int) (0 :: int))"
  sorry
end
