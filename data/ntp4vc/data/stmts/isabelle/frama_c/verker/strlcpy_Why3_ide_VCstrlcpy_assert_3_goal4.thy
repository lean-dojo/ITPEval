theory strlcpy_Why3_ide_VCstrlcpy_assert_3_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/Compound_Compound"
begin
theorem goal4:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = l_strlen t_2 a; a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 i_1; a_4 :: addr \<Rightarrow> int = a_3(shift a_1 i_1 := 0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> t_2 (shift a x_2) = (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> is_uint64 x_2 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> p_valid_str t a_4 a_1 \<longrightarrow> (if i \<le> x_2 then to_uint64 (i - (1 :: int)) = i_1 else x_2 = i_1) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x_2 \<longrightarrow> \<not>t_2 (shift a i_2) = (0 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> a_3 (shift a_1 i_2) = a_3 (shift a i_2)) \<longrightarrow> l_strlen a_4 a_1 = i_1"
  sorry
end
