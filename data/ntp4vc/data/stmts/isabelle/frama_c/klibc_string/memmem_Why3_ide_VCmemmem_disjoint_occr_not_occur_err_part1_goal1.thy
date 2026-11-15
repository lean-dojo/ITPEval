theory memmem_Why3_ide_VCmemmem_disjoint_occr_not_occur_err_part1_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound"
begin
theorem goal1:
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  shows "let a_4 :: addr = shift a_2 (0 :: int); a_5 :: addr = shift a_3 (0 :: int) in (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_4 i_1 \<longrightarrow> valid_rw t a_5 i \<longrightarrow> separated a_5 i a_4 i_1 \<longrightarrow> i = (0 :: int) \<or> i_1 = (0 :: int) \<or> i < i_1 \<or> \<not>i = (0 :: int) \<and> \<not>i_1 = (0 :: int) \<and> i_1 \<le> i \<or> (\<exists>(i_2 :: int). (0 :: int) \<le> i_2 \<and> i_2 + i_1 \<le> i \<and> (\<forall>(i_3 :: int). t_1 (shift a_1 (i_3 + i_2)) = t_1 (shift a i_3) \<or> i_3 < (0 :: int) \<or> i_1 \<le> i_3))"
  sorry
end
