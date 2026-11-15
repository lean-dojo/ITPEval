theory memb_alloc_Why3_ide_VCmemb_alloc_free_found_post_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal15:
  fixes a_1 :: "addr"
  fixes t_4 :: "addr \<Rightarrow> addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  shows "let a_2 :: addr = shift a_1 (2 :: int); a_3 :: addr = t_4 a_2; a_4 :: addr = shift a_1 (1 :: int); x :: int = t_1 a_4; a_5 :: addr = shift a_1 (0 :: int); x_1 :: int = t_1 a_5; a_6 :: addr = shift a_3 i_2; a_7 :: addr = shift a_1 (3 :: int); a_8 :: addr = t_4 a_7; x_2 :: int = i_2 * x_1 in t_3 (shift a_3 i) = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i < x \<longrightarrow> i_1 \<le> x \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_4 \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_uint16 x \<longrightarrow> is_uint16 x_1 \<longrightarrow> p_valid_memb t t_4 t_1 a_1 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> (if i_1 < x then i_2 = i_1 \<and> t_3 a_6 = (0 :: int) \<and> t_3(a_6 := 1 :: int) = t_2 \<and> shift a_8 x_2 = a \<and> -(2147483648 :: int) \<le> x_2 \<and> x_2 \<le> (2147483647 :: int) \<and> valid_rd t a_2 (1 :: int) \<and> valid_rd t a_7 (1 :: int) \<and> valid_rd t a_5 (1 :: int) \<and> valid_rd t a_6 (1 :: int) \<and> valid_rw t a_6 (1 :: int) else t_3 = t_2 \<and> Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> \<not>t_3 (shift a_3 i_3) = (0 :: int)) \<longrightarrow> (\<exists>(i_3 :: int). let a_9 :: addr = shift a_3 i_3 in t_2 a_9 = (1 :: int) \<and> t_3 a_9 = (0 :: int) \<and> shift a_8 (i_3 * x_1) = a \<and> (0 :: int) \<le> i_3 \<and> i_3 < x \<and> (\<forall>(i_4 :: int). let a_10 :: addr = shift a_3 i_4 in (0 :: int) \<le> i_4 \<and> i_4 < i_3 \<or> i_3 < i_4 \<and> i_4 < x \<longrightarrow> t_3 a_10 = t_2 a_10))"
  sorry
end
