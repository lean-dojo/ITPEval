theory strndup_Why3_ide_VCstrndup_call_memcpy_pre_4_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound"
begin
theorem goal5:
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = to_uint32 ((1 :: int) + i_1); a_2 :: addr = shift a (0 :: int) in \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_2 i \<longrightarrow> ((0 :: int) < x \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) x) \<longrightarrow> ((\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> \<not>t_1 (shift a i_2) = (0 :: int)) \<longrightarrow> i_1 = i) \<longrightarrow> ((\<exists>(i_2 :: int). t_1 (shift a i_2) = (0 :: int) \<and> (0 :: int) \<le> i_2 \<and> i_2 < i) \<longrightarrow> i_1 \<le> i) \<longrightarrow> valid_rw t a_2 i_1"
  sorry
end
