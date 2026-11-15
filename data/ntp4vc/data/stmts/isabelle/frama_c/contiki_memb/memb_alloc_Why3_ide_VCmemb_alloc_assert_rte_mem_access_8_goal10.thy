theory memb_alloc_Why3_ide_VCmemb_alloc_assert_rte_mem_access_8_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal10:
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); a_2 :: addr = t_3 a_1; a_3 :: addr = shift a_2 i; a_4 :: addr = shift a (1 :: int); x :: int = t_1 a_4 in t_2 a_3 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> i \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint16 x \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> \<not>t_2 (shift a_2 i_1) = (0 :: int)) \<longrightarrow> valid_rd t (shift a (0 :: int)) (1 :: int)"
  sorry
end
