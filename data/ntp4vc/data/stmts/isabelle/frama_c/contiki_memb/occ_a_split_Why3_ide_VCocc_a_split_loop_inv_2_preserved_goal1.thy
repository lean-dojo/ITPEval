theory occ_a_split_Why3_ide_VCocc_a_split_loop_inv_2_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes t :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  shows "let x :: int = l_occ_a t i_3 a i_2 i_4; x_1 :: int = (1 :: int) + i_1 in x + l_occ_a t i_3 a i_4 i_1 = l_occ_a t i_3 a i_2 i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> i_4 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> i_4 \<le> i_1 \<longrightarrow> i_2 \<le> i_4 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (2147483646 :: int) \<longrightarrow> sconst t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 i_4 \<longrightarrow> is_sint32 x_1 \<longrightarrow> x + l_occ_a t i_3 a i_4 x_1 = l_occ_a t i_3 a i_2 x_1"
  sorry
end
