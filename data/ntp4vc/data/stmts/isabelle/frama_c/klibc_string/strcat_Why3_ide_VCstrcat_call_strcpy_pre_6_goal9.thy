theory strcat_Why3_ide_VCstrcat_call_strcpy_pre_6_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Length_A_Length" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic1_Axiomatic1"
begin
theorem goal9:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  shows "let x :: int = base a_2; x_1 :: int = t_1 a; a_3 :: addr = shift a_2 (0 :: int); x_2 :: int = l_length t_1 a_1; x_3 :: int = l_length t_1 a_2; a_4 :: addr = shift a_1 (0 :: int); x_4 :: int = (1 :: int) + x_2 in region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_3 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_2 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_4 \<longrightarrow> valid_rw t a_3 (x_2 + x_3) \<longrightarrow> separated a_3 ((1 :: int) + x_3) a_4 x_4 \<longrightarrow> ((\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < x_3 \<longrightarrow> \<not>t_1 (shift a_2 i_5) = (0 :: int)) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> ((\<exists>(i_5 :: int). t_1 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_3) \<longrightarrow> x_1 = (0 :: int)) \<longrightarrow> ((\<exists>(i_5 :: int). t_1 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_3) \<longrightarrow> x = base a) \<longrightarrow> ((\<exists>(i_5 :: int). t_1 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_3) \<longrightarrow> p_exists_first_occurence_of_char t t_1 a_2 (0 :: int) (offset a - offset a_2)) \<longrightarrow> ((\<exists>(i_5 :: int). t_1 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_3) \<longrightarrow> addr_le a_2 a \<and> addr_le a (shift a_2 x_3)) \<longrightarrow> separated a_4 x_4 (shift a (0 :: int)) x_4"
  sorry
end
