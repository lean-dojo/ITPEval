theory memb_free_Why3_ide_VCmemb_free_loop_inv_established_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a_1 (1 :: int)) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint16 x \<longrightarrow> p_valid_memb t t_3 t_1 a_1 \<longrightarrow> valid_rd t (shift a_1 (3 :: int)) (1 :: int) \<longrightarrow> (0 :: int) \<le> x"
  sorry
end
