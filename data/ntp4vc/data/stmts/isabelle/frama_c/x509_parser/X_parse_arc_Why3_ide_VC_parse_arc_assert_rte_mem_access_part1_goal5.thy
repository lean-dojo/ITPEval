theory X_parse_arc_Why3_ide_VC_parse_arc_assert_rte_mem_access_part1_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits" "../../lib/isabelle/Compound_Compound"
begin
theorem goal5:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = base a_2 in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>a_2 = a \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x_2 = x \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> i_2 < lsl (1 :: int) (to_uint32 ((7 :: int) * i)) \<longrightarrow> i \<le> (3 :: int) \<longrightarrow> i \<le> (4 :: int) \<longrightarrow> (5 :: int) \<le> i_1 \<longrightarrow> lsl i_2 (7 :: int) \<le> (4294967295 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> bit_test (t_1 (shift a_1 i_3)) (7 :: int)) \<longrightarrow> valid_rd t (shift a_1 i) (1 :: int)"
  sorry
end
