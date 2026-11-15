theory memb_free_Why3_ide_VCmemb_free_loop_inv_5_preserved_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal8:
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (3 :: int); a_2 :: addr = t_3 a_1; a_3 :: addr = shift a (0 :: int); x :: int = t_1 a_3; x_1 :: int = i_1 * x; a_4 :: addr = l__memb_ptr t_3 t_1 a i; a_5 :: addr = shift a (1 :: int); x_2 :: int = t_1 a_5 in \<not>shift a_2 x_1 = a_4 \<longrightarrow> l__memb_index t_3 t_1 a a_4 = i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i < x_2 \<longrightarrow> i \<le> x_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> i \<le> (2147483646 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint16 x_2 \<longrightarrow> is_uint16 x \<longrightarrow> is_sint32 ((1 :: int) + i) \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_5 (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> \<not>(\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> \<not>x_1 = i_2 * x)"
  sorry
end
