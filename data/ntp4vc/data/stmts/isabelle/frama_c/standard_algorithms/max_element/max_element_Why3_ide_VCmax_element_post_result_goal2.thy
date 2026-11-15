theory max_element_Why3_ide_VCmax_element_post_result_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound"
begin
theorem goal2:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "i \<le> (0 :: int)"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "is_uint32 i"
  assumes fact4: "valid_rd t (shift a (0 :: int)) i"
  shows "(0 :: int) \<le> i"
  sorry
end
