theory get_length_Why3_ide_VCget_length_assert_rte_mem_access_4_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits" "../../lib/isabelle/Compound_Compound"
begin
theorem goal14:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = base a_2; a_3 :: addr = shift a_1 (0 :: int); x_3 :: int = t_1 a_3 in \<not>i = (0 :: int) \<longrightarrow> \<not>a_2 = a \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x_2 = x \<longrightarrow> \<not>x_3 = (128 :: int) \<longrightarrow> land (127 :: int) x_3 = (2 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> (3 :: int) \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> is_uint8 x_3 \<longrightarrow> bit_test x_3 (7 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_3 i) \<longrightarrow> valid_rd t (shift a_1 (2 :: int)) (1 :: int)"
  sorry
end
