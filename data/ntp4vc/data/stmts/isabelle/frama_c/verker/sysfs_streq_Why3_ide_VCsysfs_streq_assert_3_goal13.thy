theory sysfs_streq_Why3_ide_VCsysfs_streq_assert_3_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_SysfsStr_A_SysfsStr" "../../lib/isabelle/A_StrnCmp_A_StrnCmp" "../../lib/isabelle/A_Strnlen_A_Strnlen"
begin
theorem goal13:
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a i; a_3 :: addr = shift a_1 i in t_1 a_2 = (0 :: int) \<longrightarrow> t_1 a_3 = (0 :: int) \<longrightarrow> i \<le> l_strlen t_1 a \<longrightarrow> i \<le> l_strlen t_1 a_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_strnequal t_1 a_1 a i \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> t_1 (shift a_1 i_1) = t_1 (shift a i_1)) \<longrightarrow> (\<forall>(i_1 :: int). let x :: int = t_1 (shift a i_1); x_1 :: int = t_1 (shift a_1 i_1) in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> \<not>x = (0 :: int) \<and> \<not>x_1 = (0 :: int) \<and> x_1 = x) \<longrightarrow> l_sysfs_strlen t_1 a_1 = l_sysfs_strlen t_1 a"
  sorry
end
