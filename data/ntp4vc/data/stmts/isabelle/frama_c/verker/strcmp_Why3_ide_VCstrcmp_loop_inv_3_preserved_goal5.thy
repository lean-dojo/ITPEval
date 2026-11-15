theory strcmp_Why3_ide_VCstrcmp_loop_inv_3_preserved_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_StrCmp_A_StrCmp" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal5:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = to_uint8 x; x_2 :: int = t_1 a_2; x_3 :: int = offset a_2; x_4 :: int = offset a_3; x_5 :: int = l_strlen t_1 a_3; x_6 :: int = x_3 - x_4; x_7 :: int = t_1 (shift a_3 x_6); x_8 :: int = t_1 (shift a_1 x_6); a_4 :: addr = shift a_1 (l_strlen t_1 a_1); a_5 :: addr = shift a (1 :: int) in \<not>x_1 = (0 :: int) \<longrightarrow> to_uint8 x_2 = x_1 \<longrightarrow> l_strcmp t_1 a_3 a_1 = l_strcmp t_1 a_2 a \<longrightarrow> offset a_1 + x_3 = offset a + x_4 \<longrightarrow> x_4 + x_5 = x_3 + l_strlen t_1 a_2 \<longrightarrow> x_7 = x_8 \<longrightarrow> ((\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i \<le> x_5 \<longrightarrow> to_uint8 (t_1 (shift a_3 i)) = to_uint8 (t_1 (shift a_1 i))) \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i \<le> x_5 \<longrightarrow> t_1 (shift a_3 i) = t_1 (shift a_1 i))) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> addr_le a a_4 \<longrightarrow> addr_le a_2 (shift a_3 x_5) \<longrightarrow> is_sint8 x_8 \<longrightarrow> is_sint8 x_7 \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i + x_4 < x_3 \<longrightarrow> t_1 (shift a_3 i) = t_1 (shift a_1 i)) \<longrightarrow> addr_le a_1 a_5 \<and> addr_le a_5 a_4"
  sorry
end
