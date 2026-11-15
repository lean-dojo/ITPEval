theory X_fwrite_Why3_ide_VC_fwrite_call___fflush_pre_part1_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic3_Axiomatic3"
begin
theorem goal15:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_5 :: "addr"
  fixes i_3 :: "int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes i_4 :: "int"
  fixes a_4 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let x :: int = t_1 (shift a_5 (10 :: int)); a_6 :: addr = shift a_5 (0 :: int) in \<not>i_3 = (0 :: int) \<longrightarrow> shift a_2 (0 :: int) = shift a (0 :: int) \<longrightarrow> \<not>x = (1 :: int) \<longrightarrow> \<not>x = (2 :: int) \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_3 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_5 \<longrightarrow> valid_rw t (shift a_4 (0 :: int)) i_3 \<longrightarrow> p_valid_io_file_pvt t t_3 (t_1(shift a_6 (2 :: int) := i_2, shift a_6 (1 :: int) := i_1, shift a_5 (8 :: int) := i)) a_5"
  sorry
end
