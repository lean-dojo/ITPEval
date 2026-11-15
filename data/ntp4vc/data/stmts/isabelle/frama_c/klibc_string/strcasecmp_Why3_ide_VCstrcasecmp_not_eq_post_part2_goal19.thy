theory strcasecmp_Why3_ide_VCstrcasecmp_not_eq_post_part2_goal19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Length_A_Length" "../../lib/isabelle/A_ToUpper_A_ToUpper" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic2_Axiomatic2"
begin
theorem goal19:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_5 :: "int"
  fixes i_6 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  shows "let x :: int = base a; x_1 :: int = offset a_1; x_2 :: int = offset a; a_3 :: addr = shift a_2 (x_1 - x_2); x_3 :: int = t_1 a_1; x_4 :: int = l_length t_1 a; x_5 :: int = l_length t_1 a_2; x_6 :: int = to_uint8 x_3 in base a_1 = x \<longrightarrow> \<not>l_toupper (to_uint8 (t_1 (shift a_2 i_5))) = l_toupper (to_uint8 (t_1 (shift a i_5))) \<longrightarrow> t_1 a_3 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> i_5 \<le> i_6 \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_3 \<le> (255 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a a_1 \<longrightarrow> is_sint8 x_3 \<longrightarrow> p_length_of_str_is t t_1 a i_1 \<longrightarrow> p_length_of_str_is t t_1 a i_4 \<longrightarrow> p_length_of_str_is t t_1 a i_6 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_2 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_3 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_6 \<longrightarrow> addr_le a_1 (shift a x_4) \<longrightarrow> separated (shift a_2 (0 :: int)) ((1 :: int) + x_5) (shift a (0 :: int)) ((1 :: int) + x_4) \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> addr_le a_3 (shift a_2 x_5) \<longrightarrow> (p_is_lower (0 :: int) \<longrightarrow> i = -(32 :: int)) \<longrightarrow> (p_is_upper (0 :: int) \<longrightarrow> i = (0 :: int)) \<longrightarrow> (\<not>p_is_lower (0 :: int) \<longrightarrow> \<not>p_is_upper (0 :: int) \<longrightarrow> i = (0 :: int)) \<longrightarrow> (p_is_upper x_6 \<longrightarrow> x_3 = i) \<longrightarrow> (p_is_lower x_6 \<longrightarrow> x_3 = (32 :: int) + i) \<longrightarrow> (\<not>p_is_lower x_6 \<longrightarrow> \<not>p_is_upper x_6 \<longrightarrow> x_3 = i) \<longrightarrow> \<not>(\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 + x_2 < x_1 \<longrightarrow> l_toupper (to_uint8 (t_1 (shift a_2 i_7))) = l_toupper (to_uint8 (t_1 (shift a i_7))))"
  sorry
end
