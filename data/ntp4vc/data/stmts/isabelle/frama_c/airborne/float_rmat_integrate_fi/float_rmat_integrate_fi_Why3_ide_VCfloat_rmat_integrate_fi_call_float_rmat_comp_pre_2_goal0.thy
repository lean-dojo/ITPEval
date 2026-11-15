theory float_rmat_integrate_fi_Why3_ide_VCfloat_rmat_integrate_fi_call_float_rmat_comp_pre_2_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Axiomatic15_Axiomatic15" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S5_FloatRMat_S5_FloatRMat"
begin
theorem goal0:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> real"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "valid_rw t a (9 :: int)"
  assumes fact4: "p_rvalid_floatrates t t_1 a_1"
  assumes fact5: "is_float32 (t_1 (shift a_1 (0 :: int)))"
  assumes fact6: "is_float32 (t_1 (shift a_1 (1 :: int)))"
  assumes fact7: "is_float32 (t_1 (shift a_1 (2 :: int)))"
  shows "p_rvalid_floatrmat t t_1 a"
  sorry
end
