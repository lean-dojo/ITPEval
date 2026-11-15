theory HeapMaximum_Why3_ide_VCHeapMaximum_loop_inv_2_preserved_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal2:
  fixes t :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let x :: int = t (shift a (0 :: int)) in (0 :: int) < i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (4294967294 :: int) \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> p_isheap t a i \<longrightarrow> is_uint32 ((1 :: int) + i_1) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> t (shift a i_3) \<le> x) \<longrightarrow> t (shift a i_2) \<le> x"
  sorry
end
