theory strncpy_Why3_ide_VCstrncpy_not_exceed_post_2_goal19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_Strnlen_A_Strnlen"
begin
theorem goal19:
  fixes a_3 :: "addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  shows "let x :: int = base a_3; x_1 :: int = base a_1; a_4 :: addr = shift a_1 (0 :: int); x_2 :: int = offset a_1; x_3 :: int = offset a; x_4 :: int = x_3 - x_2 in \<not>x = x_1 \<longrightarrow> havoc t_1 t_2 a_4 ((1 :: int) + l_strnlen t_3 a_3 (0 :: int)) = t_3 \<longrightarrow> x_2 \<le> x_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> x_3 < x_2 + l_strlen t_2 a_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> p_valid_str t t_2 a_3 \<longrightarrow> p_valid_str t t_3 a_2 \<longrightarrow> is_uint64 x_4 \<longrightarrow> p_valid_strn t t_2 a_3 x_4 \<longrightarrow> p_valid_strn t t_3 a x_4 \<longrightarrow> addr_le a (shift a_1 x_4) \<longrightarrow> addr_le a_2 (shift a_3 (l_strnlen t_3 a_3 x_4)) \<longrightarrow> valid_rw t a_4 ((1 :: int) + l_strnlen t_2 a_3 x_4) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i + offset a_3 < offset a_2 \<longrightarrow> t_3 (shift a_3 i) = t_3 (shift a_1 i)) \<longrightarrow> p_valid_strn t t_3 a_1 x_4"
  sorry
end
