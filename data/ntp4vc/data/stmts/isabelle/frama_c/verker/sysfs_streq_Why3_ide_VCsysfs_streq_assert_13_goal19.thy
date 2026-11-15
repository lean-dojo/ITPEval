theory sysfs_streq_Why3_ide_VCsysfs_streq_assert_13_goal19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_SysfsStr_A_SysfsStr" "../../lib/isabelle/A_StrnCmp_A_StrnCmp" "../../lib/isabelle/A_Strnlen_A_Strnlen"
begin
theorem goal19:
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a i; a_3 :: addr = shift a_1 i; x :: int = l_sysfs_strlen t_1 a_3 in t_1 a_2 = (0 :: int) \<longrightarrow> t_1 a_3 = (10 :: int) \<longrightarrow> x = l_sysfs_strlen t_1 a_2 \<longrightarrow> t_1 (shift a_1 ((1 :: int) + i)) = (0 :: int) \<longrightarrow> i \<le> l_strlen t_1 a \<longrightarrow> i \<le> l_strlen t_1 a_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_strnequal t_1 a_1 a i \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> p_strnequal t_1 a_3 a_2 x \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> t_1 (shift a_1 i_1) = t_1 (shift a i_1)) \<longrightarrow> (\<forall>(i_1 :: int). let x_1 :: int = t_1 (shift a i_1); x_2 :: int = t_1 (shift a_1 i_1) in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> \<not>x_1 = (0 :: int) \<and> \<not>x_2 = (0 :: int) \<and> x_2 = x_1) \<longrightarrow> l_sysfs_strlen t_1 a_1 = i"
  sorry
end
