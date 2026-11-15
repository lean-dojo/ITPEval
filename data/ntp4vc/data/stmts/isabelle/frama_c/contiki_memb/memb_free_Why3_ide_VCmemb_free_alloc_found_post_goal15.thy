theory memb_free_Why3_ide_VCmemb_free_alloc_found_post_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal15:
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_5 :: "addr \<Rightarrow> addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes t_1 :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (1 :: int); x :: int = t_2 a_2; a_3 :: addr = shift a_1 (3 :: int); a_4 :: addr = shift a_1 (2 :: int); a_5 :: addr = shift (t_5 a_4) i_1 in l__memb_index t_5 t_2 a_1 (l__memb_ptr t_5 t_2 a_1 i) = i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_5 \<longrightarrow> linked t \<longrightarrow> sconst t_4 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint16 x \<longrightarrow> p_valid_memb t t_5 t_2 a_1 \<longrightarrow> p__memb_has t_5 t_2 a_1 a \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> p__memb_allocated t_5 t_4 t_2 a_1 a \<longrightarrow> (if i < x then i_1 = i \<and> t_1 = t \<and> l__memb_ptr t_5 t_2 a_1 i_1 = a \<and> t_4(a_5 := 0 :: int) = t_3 \<and> valid_rd t_1 a_4 (1 :: int) \<and> valid_rd t_1 a_5 (1 :: int) \<and> valid_rw t_1 a_5 (1 :: int) else t_4 = t_3) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> \<not>shift (t_5 a_3) (i_2 * t_2 (shift a_1 (0 :: int))) = a) \<longrightarrow> \<not>p__memb_allocated t_5 t_3 t_2 a_1 a"
  sorry
end
