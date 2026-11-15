theory binary_search_Why3_ide_VCbinary_search_post_result_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Compound_Compound"
begin
theorem goal0:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  shows "let a_1 :: addr = shift a i_2; x :: int = t_1 a_1 in i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_3 \<longrightarrow> p_sorted_1' t_1 a (0 :: int) i_1 \<longrightarrow> is_sint32 x \<longrightarrow> p_lowerbound_1' t_1 a i_2 i_1 i \<longrightarrow> p_strictupperbound_1' t_1 a (0 :: int) i_2 i \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> (if i_2 < i_1 then valid_rd t a_1 (1 :: int) \<and> (if x \<le> i then i_3 = (1 :: int) else i_3 = (0 :: int)) else i_3 = (0 :: int)) \<longrightarrow> (\<exists>(i_4 :: int). t_1 (shift a i_4) = i \<and> (0 :: int) \<le> i_4 \<and> i_4 < i_1) \<longleftrightarrow> \<not>i_3 = (0 :: int)"
  sorry
end
