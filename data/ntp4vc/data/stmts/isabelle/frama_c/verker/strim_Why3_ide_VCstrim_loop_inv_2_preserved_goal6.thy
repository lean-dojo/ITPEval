theory strim_Why3_ide_VCstrim_loop_inv_2_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Ctype_A_Ctype"
begin
theorem goal6:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x :: int = l_strlen t_1 a; a_3 :: addr = shift a (x - (1 :: int)); x_1 :: int = t_1 a_3; x_2 :: int = t_1 a_1 in \<not>i = (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> t_1 (shift a x) = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> (0 :: int) < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i \<longrightarrow> addr_le a a_1 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_isspace x_2 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> is_uint64 x \<longrightarrow> addr_lt (shift a_1 (-(1 :: int))) a_2 \<longrightarrow> addr_le (shift a (-(1 :: int))) a_1 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x_1 \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x \<longrightarrow> \<not>t_1 (shift a i_1) = (0 :: int)) \<longrightarrow> (\<forall>(a_4 :: addr). addr_lt a_1 a_4 \<longrightarrow> addr_le a_4 a_3 \<longrightarrow> p_isspace (t_1 a_4)) \<longrightarrow> p_isspace (t_2 a_2)"
  sorry
end
