theory memccpy_Why3_ide_VCmemccpy_exists_c_post_part1_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal16:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_2 (shift a i_2); a_2 :: addr = shift a_1 (0 :: int); x_1 :: int = i_1 - i; a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 x_1; a_4 :: addr = shift a x_1; a_5 :: addr = shift a (0 :: int); a_6 :: addr = shift a_1 x_1; a_7 :: addr \<Rightarrow> int = a_3(a_6 := x) in \<not>i = (0 :: int) \<longrightarrow> x = to_sint8 i_3 \<longrightarrow> a_3 a_4 = x \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_3 \<longrightarrow> i_3 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_3 \<longrightarrow> valid_rw t a_5 i_1 \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> separated a_5 i_1 a_2 i_1 \<longrightarrow> addr_le a a_4 \<longrightarrow> addr_le a_1 a_6 \<longrightarrow> addr_le a_4 (shift a i_1) \<longrightarrow> addr_le a_6 (shift a_1 i_1) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + i < i_1 \<longrightarrow> a_3 (shift a_1 i_4) = a_3 (shift a i_4)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + i < i_1 \<longrightarrow> \<not>a_3 (shift a_1 i_4) = x) \<longrightarrow> a_7 a_4 = x \<and> (0 :: int) < i \<and> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + i \<le> i_1 \<longrightarrow> a_7 (shift a_1 i_4) = a_7 (shift a i_4)) \<and> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + i < i_1 \<longrightarrow> \<not>a_7 (shift a i_4) = x)"
  sorry
end
