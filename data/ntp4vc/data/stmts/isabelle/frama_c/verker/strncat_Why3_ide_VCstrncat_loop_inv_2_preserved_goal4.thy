theory strncat_Why3_ide_VCstrncat_loop_inv_2_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strlen_A_Strlen" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strnlen_A_Strnlen"
begin
theorem goal4:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_2; x_1 :: int = l_strlen t_1 a; a_3 :: addr = shift a x_1; x_2 :: int = l_strnlen t_1 a_1 i; x_3 :: int = t_1 (shift a_1 x_2) in \<not>i = (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> t_1 a_3 = (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i + x_1 \<le> (18446744073709551615 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a a_2 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> is_uint64 x_1 \<longrightarrow> p_valid_strn t t_1 a_1 i \<longrightarrow> is_uint64 x_2 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x_3 \<longrightarrow> valid_rw t (shift a (0 :: int)) ((1 :: int) + i + x_1) \<longrightarrow> ((\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> \<not>t_1 (shift a_1 i_1) = (0 :: int)) \<longrightarrow> x_2 = i) \<longrightarrow> ((\<exists>(i_1 :: int). t_1 (shift a_1 i_1) = (0 :: int) \<and> (0 :: int) \<le> i_1 \<and> i_1 \<le> i) \<longrightarrow> x_3 = (0 :: int)) \<longrightarrow> ((\<exists>(i_1 :: int). t_1 (shift a_1 i_1) = (0 :: int) \<and> (0 :: int) \<le> i_1 \<and> i_1 \<le> i) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x_2 \<longrightarrow> \<not>t_1 (shift a_1 i_1) = (0 :: int))) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x_1 \<longrightarrow> \<not>t_1 (shift a i_1) = (0 :: int)) \<longrightarrow> p_valid_str t t_1 (shift a_2 (1 :: int))"
  sorry
end
