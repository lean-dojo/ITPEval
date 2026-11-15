theory strlen_Why3_ide_VCstrlen_loop_inv_3_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strlen_A_Strlen" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal6:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = l_strlen t_1 a_1; x_2 :: int = offset a_1 + x_1; x_3 :: int = offset a in \<not>x = (0 :: int) \<longrightarrow> x_2 = x_3 + l_strlen t_1 a \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_le a (shift a_1 x_1) \<longrightarrow> (1 :: int) + x_3 + l_strlen t_1 (shift a (1 :: int)) = x_2"
  sorry
end
