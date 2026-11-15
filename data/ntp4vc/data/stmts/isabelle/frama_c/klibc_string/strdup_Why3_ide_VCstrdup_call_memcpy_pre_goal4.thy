theory strdup_Why3_ide_VCstrdup_call_memcpy_pre_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "../../lib/isabelle/A_Length_A_Length" "../../lib/isabelle/Axiomatic_Axiomatic" "../../lib/isabelle/Compound_Compound"
begin
theorem goal4:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let x :: int = l_length t_1 a; x_1 :: int = (1 :: int) + x; x_2 :: int = to_uint32 x_1; a_2 :: addr = shift a_1 (0 :: int) in \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 x \<longrightarrow> p_length_of_str_is t t_1 a i \<longrightarrow> p_length_of_str_is t t_1 a i_1 \<longrightarrow> p_length_of_str_is t t_1 a i_2 \<longrightarrow> is_sint32 x_1 \<longrightarrow> ((0 :: int) < x_2 \<longrightarrow> valid_rw t a_2 x_2) \<longrightarrow> separated (shift a (0 :: int)) x_2 a_2 x_2"
  sorry
end
