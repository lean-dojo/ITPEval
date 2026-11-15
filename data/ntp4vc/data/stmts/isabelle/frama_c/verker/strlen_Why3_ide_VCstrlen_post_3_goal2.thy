theory strlen_Why3_ide_VCstrlen_post_3_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a_1; x_1 :: int = l_strlen t_1 a_1; x_2 :: int = offset a; x_3 :: int = to_uint64 (x_2 - x) in t_1 a = (0 :: int) \<longrightarrow> x + x_1 = x_2 + l_strlen t_1 a \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i < x_3 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_le a (shift a_1 x_1) \<longrightarrow> is_sint8 (t_1 (shift a_1 x_3)) \<longrightarrow> \<not>t_1 (shift a_1 i) = (0 :: int)"
  sorry
end
