theory X__tolower_Why3_ide_VC__tolower_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "../../lib/isabelle/Axiomatic3_Axiomatic3" "../../lib/isabelle/A_Ctype_A_Ctype" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  assumes fact0: "p_isupper (to_sint8 i_1) \<longleftrightarrow> \<not>i = (0 :: int)"
  assumes fact1: "is_uint8 i"
  assumes fact2: "is_uint8 i_1"
  assumes fact3: "is_uint8 i_2"
  assumes fact4: "if i = (0 :: int) then i_2 = i_1 else to_uint8 ((32 :: int) + i_1) = i_2"
  shows "l_tolower i_1 = i_2"
  sorry
end
