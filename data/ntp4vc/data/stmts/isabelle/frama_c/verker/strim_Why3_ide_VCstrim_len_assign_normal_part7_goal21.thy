theory strim_Why3_ide_VCstrim_len_assign_normal_part7_goal21
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Ctype_A_Ctype"
begin
theorem goal21:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_strlen t_1 a; a_2 :: addr = shift a (x - (1 :: int)); x_1 :: int = t_1 a_2; x_2 :: int = t_2 a_1; a_3 :: addr = shift a (-(1 :: int)); a_4 :: addr = shift a_1 (1 :: int); x_3 :: int = t_1 a_1 in \<not>x = (0 :: int) \<longrightarrow> t_1 (shift a x) = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> (0 :: int) < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> is_uint64 x \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> \<not>invalid t a_4 (1 :: int) \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x_1 \<longrightarrow> (if addr_le a a_1 then \<not>p_isspace x_3 \<and> (a_3 = a_1 \<or> \<not>p_isspace x_2) else t_2 = t_1 \<and> (a_3 = a_1 \<or> \<not>p_isspace x_3)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> \<not>t_1 (shift a i) = (0 :: int)) \<longrightarrow> (\<forall>(a_5 :: addr). addr_lt a_1 a_5 \<longrightarrow> addr_le a_5 a_2 \<longrightarrow> p_isspace (t_1 a_5)) \<longrightarrow> included a_4 (1 :: int) (shift a (0 :: int)) ((1 :: int) + x)"
  sorry
end
