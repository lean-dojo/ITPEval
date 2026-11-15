theory SortedShift_Why3_ide_VCSortedShift_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i_1 \<le> i"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "is_uint32 i"
  assumes fact3: "is_uint32 i_1"
  assumes fact4: "p_sorted_1' t a i_1 i"
  shows "p_sorted_1' t (shift a i_1) (0 :: int) (i - i_1)"
  sorry
end
