theory div_Div_div2by1_invqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/compare_Compare" "../../lib/isabelle/ptralias_Alias" "../../lib/isabelle/util_UtilOld" "../../lib/isabelle/add_AddOld" "../../lib/isabelle/sub_SubOld" "../../lib/isabelle/logical_LogicalUtil" "../../lib/isabelle/logical_LogicalOld"
begin
definition reciprocal :: "64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal v d \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv uint d - ((18446744073709551615 :: int) + (1 :: int))" for v d
theorem div2by1_inv'vc:
  fixes d :: "64 word"
  fixes uh :: "64 word"
  fixes v :: "64 word"
  fixes l :: "64 word"
  fixes h :: "64 word"
  fixes ul :: "64 word"
  assumes fact0: "((18446744073709551615 :: int) + (1 :: int)) ediv (2 :: int) \<le> uint d"
  assumes fact1: "uint uh < uint d"
  assumes fact2: "reciprocal v d"
  assumes fact3: "uint l + ((18446744073709551615 :: int) + (1 :: int)) * uint h = uint v * uint uh"
  shows "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> (1 :: int)"
  and "\<forall>(sl :: 64 word) (c :: 64 word). uint sl + ((18446744073709551615 :: int) + (1 :: int)) * uint c = uint l + uint ul + (0 :: int) \<and> (0 :: int) \<le> uint c \<and> uint c \<le> (1 :: int) \<longrightarrow> ((0 :: int) \<le> uint c \<and> uint c \<le> (1 :: int)) \<and> (\<forall>(sh :: 64 word) (c' :: 64 word). uint sh + ((18446744073709551615 :: int) + (1 :: int)) * uint c' = uint uh + uint h + uint c \<and> (0 :: int) \<le> uint c' \<and> uint c' \<le> (1 :: int) \<longrightarrow> (\<forall>(o1 :: 64 word). uint o1 = (uint sh + (1 :: int)) emod ((18446744073709551615 :: int) + (1 :: int)) \<longrightarrow> (\<forall>(p :: 64 word). uint p = uint o1 * uint d emod ((18446744073709551615 :: int) + (1 :: int)) \<longrightarrow> (\<forall>(o2 :: 64 word). uint o2 = (uint ul - uint p) emod ((18446744073709551615 :: int) + (1 :: int)) \<longrightarrow> (if uint sl < uint o2 then \<forall>(o3 :: 64 word). uint o3 = (uint o1 - (1 :: int)) emod ((18446744073709551615 :: int) + (1 :: int)) \<longrightarrow> (\<forall>(o4 :: 64 word). uint o4 = (uint o2 + uint d) emod ((18446744073709551615 :: int) + (1 :: int)) \<longrightarrow> (if uint d \<le> uint o4 then uint'64_in_bounds (uint o3 + (1 :: int)) \<and> (\<forall>(o5 :: 64 word). uint o5 = uint o3 + (1 :: int) \<longrightarrow> uint'64_in_bounds (uint o4 - uint d) \<and> (\<forall>(o6 :: 64 word). uint o6 = uint o4 - uint d \<longrightarrow> uint o5 * uint d + uint o6 = uint ul + ((18446744073709551615 :: int) + (1 :: int)) * uint uh \<and> (0 :: int) \<le> uint o6 \<and> uint o6 < uint d)) else uint o3 * uint d + uint o4 = uint ul + ((18446744073709551615 :: int) + (1 :: int)) * uint uh \<and> (0 :: int) \<le> uint o4 \<and> uint o4 < uint d)) else if uint d \<le> uint o2 then uint'64_in_bounds (uint o1 + (1 :: int)) \<and> (\<forall>(o3 :: 64 word). uint o3 = uint o1 + (1 :: int) \<longrightarrow> uint'64_in_bounds (uint o2 - uint d) \<and> (\<forall>(o4 :: 64 word). uint o4 = uint o2 - uint d \<longrightarrow> uint o3 * uint d + uint o4 = uint ul + ((18446744073709551615 :: int) + (1 :: int)) * uint uh \<and> (0 :: int) \<le> uint o4 \<and> uint o4 < uint d)) else uint o1 * uint d + uint o2 = uint ul + ((18446744073709551615 :: int) + (1 :: int)) * uint uh \<and> (0 :: int) \<le> uint o2 \<and> uint o2 < uint d)))))"
  sorry
end
