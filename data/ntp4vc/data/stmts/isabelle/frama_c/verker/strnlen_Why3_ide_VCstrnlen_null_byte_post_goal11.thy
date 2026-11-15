theory strnlen_Why3_ide_VCstrnlen_null_byte_post_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strnlen_A_Strnlen" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal11:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a; x_1 :: int = offset a_1; x_2 :: int = i_1 + x_1 - x; x_3 :: int = l_strnlen t_1 a_1 i_1; x_4 :: int = i_1 + x_1; x_5 :: int = t_1 (shift a_1 (to_uint64 (x - x_1))) in t_1 (shift a_1 i) = (0 :: int) \<longrightarrow> x + l_strnlen t_1 a x_2 = x_1 + x_3 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i \<le> i_1 \<longrightarrow> x_1 \<le> x \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x \<le> x_4 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> p_valid_strn t t_1 a_1 i_1 \<longrightarrow> is_uint64 x_2 \<longrightarrow> addr_le a (shift a_1 x_3) \<longrightarrow> p_valid_strn t t_1 a x_2 \<longrightarrow> is_sint8 x_5 \<longrightarrow> t_1 a = (0 :: int) \<or> x_4 = x \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x_1 < x \<longrightarrow> \<not>t_1 (shift a_1 i_2) = (0 :: int)) \<longrightarrow> x_5 = (0 :: int)"
  sorry
end
