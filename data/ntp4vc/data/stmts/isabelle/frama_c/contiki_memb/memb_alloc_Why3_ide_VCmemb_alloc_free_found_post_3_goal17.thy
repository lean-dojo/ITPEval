theory memb_alloc_Why3_ide_VCmemb_alloc_free_found_post_3_goal17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal17:
  fixes a :: "addr"
  fixes t_4 :: "addr \<Rightarrow> addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); a_2 :: addr = t_4 a_1; a_3 :: addr = shift a (1 :: int); x :: int = t_1 a_3; a_4 :: addr = shift a (0 :: int); x_1 :: int = t_1 a_4; a_5 :: addr = shift a_2 i_2; x_2 :: int = i_2 * x_1 in t_2 (shift a_2 i) = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i < x \<longrightarrow> i_1 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> framed t_4 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_uint16 x \<longrightarrow> is_uint16 x_1 \<longrightarrow> p_valid_memb t t_4 t_1 a \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> (if i_1 < x then i_2 = i_1 \<and> t_2 a_5 = (0 :: int) \<and> t_2(a_5 := 1 :: int) = t_3 \<and> -(2147483648 :: int) \<le> x_2 \<and> x_2 \<le> (2147483647 :: int) \<and> valid_rd t a_1 (1 :: int) \<and> valid_rd t (shift a (3 :: int)) (1 :: int) \<and> valid_rd t a_4 (1 :: int) \<and> valid_rd t a_5 (1 :: int) \<and> valid_rw t a_5 (1 :: int) else t_3 = t_2) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> \<not>t_2 (shift a_2 i_3) = (0 :: int)) \<longrightarrow> (1 :: int) + l__memb_numfree t_4 t_3 t_1 a = l__memb_numfree t_4 t_2 t_1 a"
  sorry
end
