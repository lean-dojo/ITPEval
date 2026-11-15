theory base_info_BaseInfo_wmpn_get_base_infoqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "mach.c_C" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/logical_LogicalUtil" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/logical_Logical" "../../lib/isabelle/ptralias_Alias"
begin
typedecl  wmpn_base_info
consts b :: "wmpn_base_info \<Rightarrow> int"
consts exp :: "wmpn_base_info \<Rightarrow> 32 word"
consts bb :: "wmpn_base_info \<Rightarrow> 64 word"
axiomatization where wmpn_base_info'invariant'0:   "(2 :: int) \<le> b self"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'1:   "b self \<le> (256 :: int)"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'2:   "uint (bb self) < (18446744073709551615 :: int) + (1 :: int)"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'3:   "(18446744073709551615 :: int) + (1 :: int) \<le> uint (bb self) * b self"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'4:   "(7 :: int) \<le> uint (exp self)"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'5:   "uint (exp self) \<le> (63 :: int)"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'6:   "uint (bb self) = b self ^\<^sub>i uint (exp self)"
  for self :: "wmpn_base_info"
definition wmpn_base_info'eq :: "wmpn_base_info \<Rightarrow> wmpn_base_info \<Rightarrow> _"
  where "wmpn_base_info'eq a b1 \<longleftrightarrow> b a = b b1 \<and> exp a = exp b1 \<and> bb a = bb b1" for a b1
axiomatization where wmpn_base_info'inj:   "a = b1"
 if "wmpn_base_info'eq a b1"
  for a :: "wmpn_base_info"
  and b1 :: "wmpn_base_info"
theorem wmpn_get_base_info'vc:
  fixes b1 :: "64 word"
  assumes fact0: "(2 :: int) \<le> uint b1"
  assumes fact1: "uint b1 \<le> (256 :: int)"
  shows "\<not>uint b1 = (0 :: int)"
  and "uint'64_in_bounds ((18446744073709551615 :: int) cdiv uint b1)"
  and "\<forall>(m :: 64 word). uint m = (18446744073709551615 :: int) cdiv uint b1 \<longrightarrow> (uint b1 ^\<^sub>i (1 :: int) = uint b1 \<and> (1 :: int) \<le> (1 :: int) \<and> (1 :: int) \<le> (64 :: int)) \<and> (\<forall>(exp1 :: 32 word) (p :: 64 word). uint b1 ^\<^sub>i uint exp1 = uint p \<and> (1 :: int) \<le> uint exp1 \<and> uint exp1 \<le> (64 :: int) \<longrightarrow> (if uint p \<le> uint m then uint'64_in_bounds (uint p * uint b1) \<and> (\<forall>(o1 :: 64 word). uint o1 = uint p * uint b1 \<longrightarrow> uint'32_in_bounds (uint exp1 + (1 :: int)) \<and> (\<forall>(o2 :: 32 word). uint o2 = uint exp1 + (1 :: int) \<longrightarrow> ((0 :: int) \<le> uint m - uint p \<and> uint m - uint o1 < uint m - uint p) \<and> uint b1 ^\<^sub>i uint o2 = uint o1 \<and> (1 :: int) \<le> uint o2 \<and> uint o2 \<le> (64 :: int))) else let o1 :: int = uint b1 in (((2 :: int) \<le> o1 \<and> o1 \<le> (256 :: int)) \<and> (uint p < (18446744073709551615 :: int) + (1 :: int) \<and> (18446744073709551615 :: int) + (1 :: int) \<le> uint p * o1) \<and> ((7 :: int) \<le> uint exp1 \<and> uint exp1 \<le> (63 :: int)) \<and> uint p = o1 ^\<^sub>i uint exp1) \<and> (\<forall>(result :: wmpn_base_info). b result = o1 \<and> exp result = exp1 \<and> bb result = p \<longrightarrow> b result = uint b1)))"
  sorry
end
