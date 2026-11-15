theory strchr_Why3_ide_VCstrchr_exists_post_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "../../lib/isabelle/A_Strchr_A_Strchr" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Strlen_A_Strlen"
begin
theorem goal10:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_3; x_1 :: int = t_1 a; x_2 :: int = t_1 a_1; a_4 :: addr = shift a_2 (l_strlen t_1 a_2) in x = to_sint8 i \<longrightarrow> l_strchr t_1 a_2 x = l_strchr t_1 a_1 x \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_2 a_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x_1 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> addr_le a_3 a_4 \<longrightarrow> (if x = x_2 then a_1 = a \<and> (a_4 = a \<longleftrightarrow> x_1 = (0 :: int)) \<and> (addr_lt a a_4 \<longleftrightarrow> \<not>x_1 = (0 :: int)) else Mk_addr (0 :: int) (0 :: int) = a \<and> x_2 = (0 :: int)) \<longrightarrow> (\<forall>(a_5 :: addr). addr_lt a_5 a_1 \<longrightarrow> addr_le a_2 a_5 \<longrightarrow> \<not>x = t_1 a_5) \<longrightarrow> addr_le a_2 a \<and> addr_le a a_4"
  sorry
end
