theory search_n_Why3_ide_VCsearch_n_has_match_post_match_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal14:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_6 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes i_7 :: "int"
  shows "let x :: int = t_1 (shift a (i - (1 :: int))); x_1 :: int = (1 :: int) + i_6; x_2 :: int = i_1 + i_2; a_1 :: addr = shift a i_6; x_3 :: int = to_uint32 x_1 in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_uint32 i_6 \<longrightarrow> is_sint32 i_7 \<longrightarrow> p_hasconstantsubrange t_1 a i_4 i_2 i_7 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_4 \<longrightarrow> is_sint32 x \<longrightarrow> (if (0 :: int) < i_2 then if i_2 \<le> i_4 then i_5 = i_3 \<and> i_5 = i_4 \<and> i \<le> x_1 \<and> p_constantrange t_1 a i i_6 i_7 \<and> \<not>p_hasconstantsubrange t_1 a i_6 i_2 i_7 \<and> (if i_6 < i_5 then i_1 = i \<and> x_2 = x_1 \<and> t_1 a_1 = i_7 \<and> i_1 \<le> x_3 \<and> i_6 \<le> (4294967294 :: int) \<and> x_3 \<le> (4294967295 :: int) + i_1 \<and> valid_rd t a_1 (1 :: int) else i_5 = i_1) \<and> ((0 :: int) < i \<longrightarrow> \<not>x = i_7) else i_4 = i_1 else i_1 = (0 :: int)) \<longrightarrow> p_constantrange t_1 a i_1 x_2 i_7"
  sorry
end
