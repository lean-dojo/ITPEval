theory memb_numfree_Why3_ide_VCmemb_numfree_loop_inv_3_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let a_1 :: addr = shift a (1 :: int); x :: int = t_1 a_1; a_2 :: addr = shift a (2 :: int); a_3 :: addr = t_3 a_2; x_1 :: int = l_occ_a t_2 (0 :: int) a_3 (0 :: int) i_2; x_2 :: int = (1 :: int) + i_2; a_4 :: addr = shift a_3 i_2; x_3 :: int = t_2 a_4 in (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> i_2 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_1 \<le> i_2 \<longrightarrow> i_2 \<le> (2147483646 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_uint16 x \<longrightarrow> is_sint32 x_2 \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> is_sint8 x_3 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> is_sint32 x_1 \<longrightarrow> (if x_3 = (0 :: int) then (1 :: int) + i = i_1 \<and> x_1 = i \<and> i \<le> (2147483646 :: int) else x_1 = i_1) \<longrightarrow> l_occ_a t_2 (0 :: int) a_3 (0 :: int) x_2 = i_1"
  sorry
end
