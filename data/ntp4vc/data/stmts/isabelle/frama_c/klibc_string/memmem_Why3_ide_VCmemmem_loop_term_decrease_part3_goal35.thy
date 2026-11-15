theory memmem_Why3_ide_VCmemmem_loop_term_decrease_part3_goal35
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound"
begin
theorem goal35:
  fixes a_8 :: "addr"
  fixes a_9 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes a_6 :: "addr"
  fixes i_1 :: "int"
  fixes a_7 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_5 :: "addr"
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  shows "let x :: int = base a_8; x_1 :: int = base a_9; x_2 :: int = t_1 (shift a_1 (0 :: int)); x_3 :: int = t_1 (shift a i_2); x_4 :: int = t_1 (shift a_1 (1 :: int)); x_5 :: int = to_uint32 ((1 :: int) + i_2); x_6 :: int = t_1 (shift a x_5); a_10 :: addr = shift a_8 (0 :: int); a_11 :: addr = shift a_9 (0 :: int); a_12 :: addr = shift a_6 (0 :: int); x_7 :: int = to_uint32 (i_1 - (2 :: int)); a_13 :: addr = shift a_7 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_1 = (1 :: int) \<longrightarrow> x = base a_1 \<longrightarrow> x_1 = base a \<longrightarrow> \<not>x_2 = x_3 \<longrightarrow> x_4 = x_2 \<longrightarrow> x_6 = x_4 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> i_2 \<le> to_uint32 (i - i_1) \<longrightarrow> i_1 + i_2 \<le> (2 :: int) + i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint8 x_3 \<longrightarrow> is_uint8 x_2 \<longrightarrow> is_uint8 x_4 \<longrightarrow> valid_rw t a_10 i_1 \<longrightarrow> valid_rw t a_11 i \<longrightarrow> separated a_11 i a_10 i_1 \<longrightarrow> valid_rw t a_12 x_7 \<longrightarrow> valid_rw t a_13 x_7 \<longrightarrow> separated a_13 x_7 a_12 x_7 \<longrightarrow> is_uint8 x_6 \<longrightarrow> ((0 :: int) < x_7 \<longrightarrow> \<not>(\<exists>(i_3 :: int). \<not>t_1 (shift a_5 i_3) = t_1 (shift a_4 i_3) \<and> (0 :: int) \<le> i_3 \<and> i_3 < x_7)) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> (\<exists>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> (3 :: int) + i_4 \<le> i_1 \<longrightarrow> \<not>t_1 (shift a_3 ((2 :: int) + i_4 + i_3)) = t_1 (shift a_2 ((2 :: int) + i_4)))) \<longrightarrow> i_2 < x_5"
  sorry
end
