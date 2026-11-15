theory float_rmat_inv_Why3_ide_VCfloat_rmat_inv_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Axiomatic15_Axiomatic15" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/S10_RealRMat_s_S10_RealRMat_s" "../../lib/isabelle/Axiomatic17_Axiomatic17"
begin
theorem goal0:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); m :: addr \<Rightarrow> real = t_1(shift a_2 (0 :: int) := t_1 (shift a_3 (0 :: int))); m_1 :: addr \<Rightarrow> real = m(shift a_2 (1 :: int) := m (shift a_3 (3 :: int))); m_2 :: addr \<Rightarrow> real = m_1(shift a_2 (2 :: int) := m_1 (shift a_3 (6 :: int))); m_3 :: addr \<Rightarrow> real = m_2(shift a_2 (3 :: int) := m_2 (shift a_3 (1 :: int))); m_4 :: addr \<Rightarrow> real = m_3(shift a_2 (4 :: int) := m_3 (shift a_3 (4 :: int))); m_5 :: addr \<Rightarrow> real = m_4(shift a_2 (5 :: int) := m_4 (shift a_3 (7 :: int))); m_6 :: addr \<Rightarrow> real = m_5(shift a_2 (6 :: int) := m_5 (shift a_3 (2 :: int))); m_7 :: addr \<Rightarrow> real = m_6(shift a_2 (7 :: int) := m_6 (shift a_3 (5 :: int))); m_8 :: addr \<Rightarrow> real = m_7(shift a_2 (8 :: int) := m_7 (shift a_3 (8 :: int))) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> valid_rw t a (9 :: int) \<longrightarrow> p_rvalid_floatrmat t t_1 a_1 \<longrightarrow> separated a (9 :: int) a_1 (9 :: int) \<longrightarrow> eqs10_realrmat_s (l_transpose (l_l_rmat_of_floatrmat m_8 a_1)) (l_l_rmat_of_floatrmat m_8 a)"
  sorry
end
