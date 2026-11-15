theory is_sorted_Why3_ide_VCis_sorted_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/Compound_Compound" "../../lib/isabelle/Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes p :: "bool"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_2; a_1 :: addr = shift a i_2 in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> (if (0 :: int) < i then p = False \<and> p_weaklysorted_1' t_1 a (0 :: int) x \<and> (if (2 :: int) + i_2 \<le> i then i_1 = (0 :: int) \<and> t_1 (shift a x) < t_1 a_1 \<and> i_2 \<le> (4294967294 :: int) \<and> valid_rd t a_1 (1 :: int) \<and> valid_rd t (shift a (to_uint32 x)) (1 :: int) else i_1 = (1 :: int)) else i_1 = (1 :: int)) \<longrightarrow> p_sorted_1' t_1 a (0 :: int) i \<longleftrightarrow> \<not>i_1 = (0 :: int)"
  sorry
end
