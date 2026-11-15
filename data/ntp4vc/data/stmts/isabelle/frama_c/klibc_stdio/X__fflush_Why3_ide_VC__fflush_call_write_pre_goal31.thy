theory X__fflush_Why3_ide_VC__fflush_call_write_pre_goal31
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "../../lib/isabelle/Compound_Compound" "Why3STD.Cint_Cint" "../../lib/isabelle/Axiomatic3_Axiomatic3"
begin
theorem goal31:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = t_2 (shift a_1 (5 :: int)); x :: int = base a_2; x_1 :: int = base a; x_2 :: int = base (t_2 (shift a_1 (6 :: int))); x_3 :: int = t_1 (shift a_1 (9 :: int)); x_4 :: int = t_1 (shift (shift a_1 (0 :: int)) (0 :: int)) in \<not>i = (0 :: int) \<longrightarrow> t_1 (shift a_1 (7 :: int)) = (0 :: int) \<longrightarrow> x = x_1 \<longrightarrow> x_2 = x_1 \<longrightarrow> x_2 = x \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i_1 \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint32 x_3 \<longrightarrow> is_uint32 (t_1 (shift a_1 (8 :: int))) \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> addr_le a_2 a \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> is_sint32 x_4 \<longrightarrow> addr_le a (shift a_2 ((32 :: int) + x_3)) \<longrightarrow> (0 :: int) \<le> x_4"
  sorry
end
