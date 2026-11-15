theory partial_sum_Why3_ide_VCpartial_sum_assert_rte_signed_overflow_2_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_AccumulateAxiomatic_A_AccumulateAxiomatic" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal14:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); x :: int = t_2 a_3; a_4 :: addr \<Rightarrow> int = havoc t_1 (t_2(a_2 := x)) (shift a (1 :: int)) (i - (1 :: int)); x_1 :: int = i_1 - (1 :: int); a_5 :: int = a_4 (shift a x_1); a_6 :: int = a_4 (shift a_1 i_1); a_7 :: int = a_4 (shift a (to_uint32 x_1)) in a_5 = l_accumulate_1' a_4 a_1 i_1 (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_3 i \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t a_2 i \<longrightarrow> p_accumulatebounds_1' t_2 a_1 ((1 :: int) + i) (0 :: int) \<longrightarrow> separated a_3 i a_2 i \<longrightarrow> is_sint32 a_6 \<longrightarrow> is_sint32 a_5 \<longrightarrow> is_sint32 a_7 \<longrightarrow> p_unchanged_1' a_4 t_2 a_1 (0 :: int) i \<longrightarrow> p_partialsum a_4 a_1 i_1 a \<longrightarrow> a_6 + a_7 \<le> (2147483647 :: int)"
  sorry
end
