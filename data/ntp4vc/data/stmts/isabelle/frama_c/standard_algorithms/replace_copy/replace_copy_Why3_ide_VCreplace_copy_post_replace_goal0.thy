theory replace_copy_Why3_ide_VCreplace_copy_post_replace_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 i_2 in i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rd t a_2 i_2 \<longrightarrow> valid_rw t a_3 i_2 \<longrightarrow> separated a_2 i_2 a (1 :: int) \<longrightarrow> p_unchanged_1' a_4 t_2 a_1 i_3 i_2 \<longrightarrow> p_replace_1' a_4 t_2 a_1 i_3 a i_1 i \<longrightarrow> p_replace_1' (havoc t_1 t_2 a_3 i_3) t_2 a_1 i_3 a i_1 i"
  sorry
end
