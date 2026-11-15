theory strnlen_Why3_ide_VCstrnlen_loop_inv_6_preserved_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strnlen_A_Strnlen" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal8:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = offset a_1; x_2 :: int = offset a; x_3 :: int = i_1 + x_2 - x_1; x_4 :: int = l_strnlen t_1 a_1 x_3 in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> x_1 + x_4 = x_2 + l_strnlen t_1 a i_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> x_1 \<le> x_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i + x_1 \<le> x_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_strn t t_1 a i_1 \<longrightarrow> is_uint64 x_3 \<longrightarrow> p_valid_strn t t_1 a_1 x_3 \<longrightarrow> addr_le a (shift a_1 x_4) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x_1 < x_2 \<longrightarrow> \<not>t_1 (shift a_1 i_2) = (0 :: int)) \<longrightarrow> \<not>t_1 (shift a_1 i) = (0 :: int)"
  sorry
end
