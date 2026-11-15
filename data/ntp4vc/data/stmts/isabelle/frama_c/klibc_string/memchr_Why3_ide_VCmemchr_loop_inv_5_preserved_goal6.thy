theory memchr_Why3_ide_VCmemchr_loop_inv_5_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal6:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (i_1 - i); x :: int = t_1 a_1; x_1 :: int = to_sint8 i_3 in \<not>i = (0 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_2 + to_uint32 (i - (1 :: int)) < i_1 \<longrightarrow> -(128 :: int) \<le> i_3 \<longrightarrow> i_3 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_3 \<longrightarrow> valid_rw t (shift a (0 :: int)) i_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_1 (shift a i_1) \<longrightarrow> is_sint8 x \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + i < i_1 \<longrightarrow> \<not>t_1 (shift a i_4) = x_1) \<longrightarrow> \<not>t_1 (shift a i_2) = x_1"
  sorry
end
