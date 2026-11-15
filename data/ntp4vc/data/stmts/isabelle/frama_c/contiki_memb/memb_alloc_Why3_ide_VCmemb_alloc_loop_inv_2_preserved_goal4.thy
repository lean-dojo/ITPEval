theory memb_alloc_Why3_ide_VCmemb_alloc_loop_inv_2_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); a_2 :: addr = t_3 a_1; a_3 :: addr = shift a_2 i; x :: int = t_2 a_3; a_4 :: addr = shift a (1 :: int); x_1 :: int = t_1 a_4 in \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i < x_1 \<longrightarrow> i \<le> x_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i \<le> (2147483646 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint16 x_1 \<longrightarrow> is_sint32 ((1 :: int) + i) \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> is_sint8 x \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> \<not>t_2 (shift a_2 i_2) = (0 :: int)) \<longrightarrow> \<not>t_2 (shift a_2 i_1) = (0 :: int)"
  sorry
end
