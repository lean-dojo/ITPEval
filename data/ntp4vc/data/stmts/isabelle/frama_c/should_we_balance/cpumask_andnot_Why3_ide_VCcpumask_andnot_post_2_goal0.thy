theory cpumask_andnot_Why3_ide_VCcpumask_andnot_post_2_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/A_thread_variables_properties_A_thread_variables_properties" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_schedule_cpumask_A_schedule_cpumask"
begin
theorem goal0:
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_3 :: addr = t_3 (shift a (0 :: int)); a_4 :: addr = shift a_3 (0 :: int); a_5 :: addr = t_3 (shift a_1 (0 :: int)); a_6 :: addr = shift a_5 (0 :: int); a_7 :: addr = t_3 (shift a_2 (0 :: int)); a_8 :: addr = shift a_7 (0 :: int); a_9 :: addr \<Rightarrow> int = havoc t_1 t_2 a_8 l_size in \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> to_uint32 i = l_size \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < l_size \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> valid_rd t a (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_4 l_size \<longrightarrow> valid_rd t a_6 l_size \<longrightarrow> valid_rw t a_8 l_size \<longrightarrow> p_idle_core t_3 a_9 i_1 \<longrightarrow> (\<not>a_2 = a \<longrightarrow> separated a_8 l_size a_4 l_size) \<longrightarrow> (\<not>a_2 = a_1 \<longrightarrow> separated a_8 l_size a_6 l_size) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < l_size \<longrightarrow> separated a_8 l_size (shift (t_3 (shift (l_cpu_smt_mask i_2) (0 :: int))) (0 :: int)) l_size) \<longrightarrow> (\<forall>(i_2 :: int). let a_10 :: addr = shift a_7 i_2 in i \<le> i_2 \<longrightarrow> i_2 < l_size \<longrightarrow> \<not>a_9 a_10 = (0 :: int) \<longleftrightarrow> \<not>t_2 a_10 = (0 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> t_2 (shift a_3 i_2) = (0 :: int) \<and> \<not>t_2 (shift a_5 i_2) = (0 :: int) \<longleftrightarrow> \<not>a_9 (shift a_7 i_2) = (0 :: int)) \<longrightarrow> p_idle_core t_3 t_2 i_1"
  sorry
end
