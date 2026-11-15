theory memb_free_Why3_ide_VCmemb_free_assert_rte_mem_access_4_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal11:
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x :: int = l__memb_index t_3 t_1 a_1 a; a_2 :: addr = shift a_1 (1 :: int); x_1 :: int = t_1 a_2; a_3 :: addr = shift a_1 (3 :: int) in l__memb_ptr t_3 t_1 a_1 x = a \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> x < x_1 \<longrightarrow> x \<le> x_1 \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint16 x_1 \<longrightarrow> p_valid_memb t t_3 t_1 a_1 \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> is_sint32 x \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> \<not>shift (t_3 a_3) (i * t_1 (shift a_1 (0 :: int))) = a) \<longrightarrow> valid_rd t (shift a_1 (2 :: int)) (1 :: int)"
  sorry
end
