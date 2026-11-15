theory match_string_Why3_ide_VCmatch_string_exists_post_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_StrCmp_A_StrCmp" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/A_MatchString_A_MatchString"
begin
theorem goal7:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_real_len t_2 a_1 i; a_2 :: addr = t_2 (shift a_1 i_1); a_3 :: addr = shift a_1 (0 :: int) in l_strcmp t_1 (t_2 (shift a_1 i_3)) a = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x \<le> i \<longrightarrow> i_3 < x \<longrightarrow> i_2 \<le> x \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_uint64 i \<longrightarrow> is_uint64 i_3 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> (if to_uint64 i_2 < i then if t_2 (shift a_1 i_2) = Mk_addr (0 :: int) (0 :: int) then i_1 = -(22 :: int) else i_2 = i_1 \<and> l_strcmp t_1 a_2 a = (0 :: int) \<and> p_valid_str t t_1 a_2 \<and> (\<forall>(i_4 :: int). t_1 (shift a_2 i_4) = t_1 (shift a i_4) \<or> i_4 < (0 :: int) \<or> l_strlen t_1 a_2 < i_4) else i_1 = -(22 :: int)) \<longrightarrow> (x = i \<longrightarrow> valid_rw t a_3 i) \<longrightarrow> (x < i \<longrightarrow> valid_rw t a_3 ((1 :: int) + x)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_2 \<longrightarrow> p_valid_str t t_1 (t_2 (shift a_1 i_4))) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_2 \<longrightarrow> \<not>l_strcmp t_1 (t_2 (shift a_1 i_4)) a = (0 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> is_uint64 i_4 \<longrightarrow> p_valid_str t t_1 (t_2 (shift a_1 i_4))) \<longrightarrow> l_match_string t_2 t_1 a_1 x a = i_1"
  sorry
end
