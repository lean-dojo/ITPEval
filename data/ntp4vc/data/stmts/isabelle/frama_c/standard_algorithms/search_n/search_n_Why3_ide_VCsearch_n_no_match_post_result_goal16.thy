theory search_n_Why3_ide_VCsearch_n_no_match_post_result_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal16:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_7 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes i_6 :: "int"
  fixes i_8 :: "int"
  shows "let x :: int = t_1 (shift a (i - (1 :: int))); x_1 :: int = (1 :: int) + i_7; a_1 :: addr = shift a i_7; x_2 :: int = i_3 + to_uint32 x_1 in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_uint32 i_6 \<longrightarrow> is_uint32 i_7 \<longrightarrow> is_sint32 i_8 \<longrightarrow> \<not>p_hasconstantsubrange t_1 a i_5 i_3 i_8 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_5 \<longrightarrow> is_sint32 x \<longrightarrow> (if (0 :: int) < i_3 then if i_3 \<le> i_5 then i_5 = i_4 \<and> i_6 = i_4 \<and> i_6 = i_5 \<and> i \<le> x_1 \<and> p_constantrange t_1 a i i_7 i_8 \<and> \<not>p_hasconstantsubrange t_1 a i_7 i_3 i_8 \<and> (if i_7 < i_5 then i + i_3 = x_1 \<and> i_1 + i_3 = x_1 \<and> i_2 + i_3 = x_1 \<and> t_1 a_1 = i_8 \<and> i_7 < x_2 \<and> i_7 \<le> (4294967294 :: int) \<and> x_2 \<le> (4294967296 :: int) + i_7 \<and> valid_rd t a_1 (1 :: int) else i_5 = i_2) \<and> ((0 :: int) < i \<longrightarrow> \<not>x = i_8) else i_5 = i_2 else i_2 = (0 :: int)) \<longrightarrow> i_5 = i_2"
  sorry
end
