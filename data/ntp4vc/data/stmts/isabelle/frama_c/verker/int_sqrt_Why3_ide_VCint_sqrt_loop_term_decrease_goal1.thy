theory int_sqrt_Why3_ide_VCint_sqrt_loop_term_decrease_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits"
begin
theorem goal1:
  fixes i_1 :: "int"
  fixes i :: "int"
  shows "let x :: int = lsr i_1 (2 :: int) in \<not>i_1 = (0 :: int) \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> is_uint64 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> is_uint64 x \<longrightarrow> x < i_1"
  sorry
end
