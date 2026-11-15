theory memb_free_Why3_ide_VCmemb_free_loop_inv_4_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal6:
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = l__memb_ptr t_3 t_1 a_1 i; a_3 :: addr = shift a_1 (1 :: int); x :: int = t_1 a_3; a_4 :: addr = shift a_1 (0 :: int); x_1 :: int = t_1 a_4; x_2 :: int = (1 :: int) + i; a_5 :: addr = shift a_1 (3 :: int) in \<not>a_2 = a \<longrightarrow> l__memb_index t_3 t_1 a_1 a_2 = i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> i \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i \<le> (2147483646 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint16 x \<longrightarrow> is_uint16 x_1 \<longrightarrow> is_sint32 x_2 \<longrightarrow> p_valid_memb t t_3 t_1 a_1 \<longrightarrow> valid_rd t a_5 (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> \<not>shift (t_3 a_5) (i_1 * x_1) = a) \<longrightarrow> x_2 = l__memb_index t_3 t_1 a_1 (l__memb_ptr t_3 t_1 a_1 x_2)"
  sorry
end
