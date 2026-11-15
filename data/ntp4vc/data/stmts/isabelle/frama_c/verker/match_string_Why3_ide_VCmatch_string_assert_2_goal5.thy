theory match_string_Why3_ide_VCmatch_string_assert_2_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_StrCmp_A_StrCmp" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/A_MatchString_A_MatchString"
begin
theorem goal5:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = t_2 (shift a_1 i_1); x :: int = l_strcmp t_1 a_2 a; x_1 :: int = t_1 (shift a_2 i_2); x_2 :: int = t_1 (shift a i_2); x_3 :: int = l_real_len t_2 a_1 i; x_4 :: int = l_strlen t_1 a_2; a_3 :: addr = shift a_1 (0 :: int) in \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> \<not>x_1 = x_2 \<longrightarrow> \<not>t_1 (shift a_2 i_3) = t_1 (shift a i_3) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> to_uint64 i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x_3 \<le> i \<longrightarrow> i_1 \<le> x_3 \<longrightarrow> i_2 \<le> x_4 \<longrightarrow> i_3 \<le> x_4 \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> is_sint32 x \<longrightarrow> (if to_uint8 x_1 < to_uint8 x_2 then x = -(1 :: int) else x = (1 :: int)) \<longrightarrow> (x_3 = i \<longrightarrow> valid_rw t a_3 i) \<longrightarrow> (x_3 < i \<longrightarrow> valid_rw t a_3 ((1 :: int) + x_3)) \<longrightarrow> x = -(1 :: int) \<or> x = (1 :: int) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_1 \<longrightarrow> p_valid_str t t_1 (t_2 (shift a_1 i_4))) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_2 \<longrightarrow> t_1 (shift a_2 i_4) = t_1 (shift a i_4)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_1 \<longrightarrow> \<not>l_strcmp t_1 (t_2 (shift a_1 i_4)) a = (0 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < x_3 \<longrightarrow> is_uint64 i_4 \<longrightarrow> p_valid_str t t_1 (t_2 (shift a_1 i_4))) \<longrightarrow> (\<exists>(i_4 :: int). \<not>t_1 (shift a_2 i_4) = t_1 (shift a i_4) \<and> (0 :: int) \<le> i_4 \<and> i_4 \<le> min (l_strlen t_1 a) x_4 \<and> is_uint64 i_4)"
  sorry
end
