theory memb_alloc_Why3_ide_VCmemb_alloc_full_post_3_goal21
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal21:
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); a_2 :: addr = t_3 a_1; a_3 :: addr = shift a_2 i; a_4 :: addr = shift a (1 :: int); x :: int = t_1 a_4; a_5 :: addr = shift a (0 :: int); x_1 :: int = t_1 a_5; x_2 :: int = i * x_1; a_6 :: addr = shift a (3 :: int) in t_2 a_3 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_2 \<longrightarrow> x_2 \<le> (2147483647 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint16 x \<longrightarrow> is_uint16 x_1 \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> p__memb_full t_3 t_2 t_1 a \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_6 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_5 (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> \<not>t_2 (shift a_2 i_1) = (0 :: int)) \<longrightarrow> shift (t_3 a_6) x_2 = Mk_addr (0 :: int) (0 :: int)"
  sorry
end
