theory memb_init_Why3_ide_VCmemb_init_call_memset_pre_valid_s_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic12_Axiomatic12"
begin
theorem goal9:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (1 :: int); x :: int = t_1 a_1; a_2 :: addr = shift a (2 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint16 x \<longrightarrow> is_uint16 (t_1 (shift a (0 :: int))) \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> p_valid_or_empty t (t_3 a_2) x"
  sorry
end
