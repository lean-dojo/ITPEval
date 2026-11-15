theory check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_9_part03_goal29
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits"
begin
theorem goal29:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a_1 (1 :: int); x :: int = t_1 a_3; a_4 :: addr = shift a_1 (2 :: int); x_1 :: int = t_1 a_4; a_5 :: addr = shift a_1 (3 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> t_1 a_2 = (244 :: int) \<longrightarrow> land (192 :: int) x = (128 :: int) \<longrightarrow> land (192 :: int) x_1 = (128 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (4 :: int) \<le> i \<longrightarrow> (128 :: int) \<le> x \<longrightarrow> x \<le> (143 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint8 x \<longrightarrow> is_uint8 x_1 \<longrightarrow> is_uint8 (t_1 a_5) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1) \<longrightarrow> valid_rd t a_5 (1 :: int)"
  sorry
end
