theory StrictLowerBoundShift_Why3_ide_VCStrictLowerBoundShift_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "addr \<Rightarrow> int"
  shows "let x :: int = i_1 + i_3 in region (base a) \<le> (0 :: int) \<longrightarrow> x \<le> (4294967295 :: int) \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> p_strictlowerbound_1' t (shift a i_3) i_2 i_1 i \<longrightarrow> p_strictlowerbound_1' t a (i_2 + i_3) x i"
  sorry
end
