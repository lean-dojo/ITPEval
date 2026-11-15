theory list_tail_Why3_ide_VClist_tail_loop_inv_3_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S1_list_S1_list" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal6:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = t_1 a; x :: int = i_1 + i_2; a_3 :: addr = t_1 (shift a_1 x); a_4 :: addr = t_1 (shift a_3 (0 :: int)); x_1 :: int = (1 :: int) + i_2 in \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a_2 a_1 i_1 i (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> p_linked_n t t_1 a_2 a_1 i_1 i_2 a_3 \<longrightarrow> p_linked_n t t_1 a_3 a_1 x (i - i_2) (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> p_linked_n t t_1 a_2 a_1 i_1 x_1 a_4"
  sorry
end
