theory match_string_Why3_ide_VCmatch_string_loop_inv_established_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_StrCmp_A_StrCmp" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/A_MatchString_A_MatchString"
begin
theorem goal1:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = l_real_len t_2 a_1 i; a_2 :: addr = shift a_1 (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> (x = i \<longrightarrow> valid_rw t a_2 i) \<longrightarrow> (x < i \<longrightarrow> valid_rw t a_2 ((1 :: int) + x)) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x \<longrightarrow> is_uint64 i_1 \<longrightarrow> p_valid_str t t_1 (t_2 (shift a_1 i_1))) \<longrightarrow> x \<le> i \<and> (0 :: int) \<le> x"
  sorry
end
