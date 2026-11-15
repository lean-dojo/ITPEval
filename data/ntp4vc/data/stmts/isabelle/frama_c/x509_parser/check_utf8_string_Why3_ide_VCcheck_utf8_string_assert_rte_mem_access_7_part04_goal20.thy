theory check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_7_part04_goal20
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal20:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); x :: int = t_1 a_2 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> \<not>x = (240 :: int) \<longrightarrow> \<not>x = (244 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (4 :: int) \<le> i \<longrightarrow> (128 :: int) \<le> x \<longrightarrow> (194 :: int) \<le> x \<longrightarrow> (224 :: int) \<le> x \<longrightarrow> (240 :: int) \<le> x \<longrightarrow> x \<le> (244 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_2 i \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1) \<longrightarrow> valid_rd t (shift a_1 (1 :: int)) (1 :: int)"
  sorry
end
