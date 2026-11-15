theory UpperBoundShift_Why3_ide_VCUpperBoundShift_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic1_Axiomatic1" "../../lib/isabelle/A_Count_A_Count" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i_2 \<le> i_1"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "is_uint32 i_1"
  assumes fact3: "is_uint32 i_2"
  assumes fact4: "is_sint32 i"
  assumes fact5: "p_upperbound_1' t (shift a i_2) (0 :: int) (i_1 - i_2) i"
  shows "p_upperbound_1' t a i_2 i_1 i"
  sorry
end
