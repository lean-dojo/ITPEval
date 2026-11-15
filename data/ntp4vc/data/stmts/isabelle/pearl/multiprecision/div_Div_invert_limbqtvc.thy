theory div_Div_invert_limbqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/compare_Compare" "../../lib/isabelle/ptralias_Alias" "../../lib/isabelle/util_UtilOld" "../../lib/isabelle/add_AddOld" "../../lib/isabelle/sub_SubOld" "../../lib/isabelle/logical_LogicalUtil" "../../lib/isabelle/logical_LogicalOld"
begin
definition reciprocal :: "64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal v d \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv uint d - ((18446744073709551615 :: int) + (1 :: int))" for v d
theorem invert_limb'vc:
  fixes d :: "64 word"
  assumes fact0: "((18446744073709551615 :: int) + (1 :: int)) ediv (2 :: int) \<le> uint d"
  shows "let o1 :: 64 word = uint'64_max in uint'64_in_bounds (uint o1 - uint d) \<and> (\<forall>(o2 :: 64 word). uint o2 = uint o1 - uint d \<longrightarrow> uint o2 < uint d \<and> (\<forall>(v :: 64 word). uint v = (uint uint'64_max + ((18446744073709551615 :: int) + (1 :: int)) * uint o2) ediv uint d \<longrightarrow> reciprocal v d))"
  sorry
end
