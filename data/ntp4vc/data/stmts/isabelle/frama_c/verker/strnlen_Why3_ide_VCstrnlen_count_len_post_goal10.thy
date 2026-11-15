theory strnlen_Why3_ide_VCstrnlen_count_len_post_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strnlen_A_Strnlen" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal10:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a_1; x_1 :: int = offset a; x_3 :: int = i + x_1 - x; x_4 :: int = l_strnlen t_1 a_1 x_3; x_5 :: int = i + x_1 in \<not>i = (0 :: int) \<longrightarrow> t_1 a = (0 :: int) \<longrightarrow> x + x_4 = x_1 + l_strnlen t_1 a i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x \<le> x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_1 a \<longrightarrow> p_valid_strn t t_1 a i \<longrightarrow> is_uint64 x_3 \<longrightarrow> p_valid_strn t t_1 a_1 x_3 \<longrightarrow> addr_le a (shift a_1 x_4) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x < x_1 \<longrightarrow> \<not>t_1 (shift a_1 i_1) = (0 :: int)) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x \<le> x_5 \<longrightarrow> \<not>t_1 (shift a_1 i_1) = (0 :: int)) \<longrightarrow> x + to_uint64 (x_1 - x) = x_5"
  sorry
end
