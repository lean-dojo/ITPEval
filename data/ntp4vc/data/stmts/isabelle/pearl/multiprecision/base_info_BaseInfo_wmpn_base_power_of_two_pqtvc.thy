theory base_info_BaseInfo_wmpn_base_power_of_two_pqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "mach.c_C" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/logical_LogicalUtil" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/logical_Logical" "../../lib/isabelle/ptralias_Alias"
begin
theorem wmpn_base_power_of_two_p'vc:
  fixes b :: "64 word"
  fixes o1 :: "bool"
  fixes result :: "32 word"
  assumes fact0: "(2 :: int) \<le> uint b"
  assumes fact1: "uint b \<le> (256 :: int)"
  assumes fact2: "uint b = uint (2 :: 64 word) \<longrightarrow> o1 = True"
  assumes fact3: "o1 = True \<longrightarrow> b = (2 :: 64 word)"
  assumes fact4: "if o1 = True then result = (1 :: 32 word) else \<exists>(o2 :: bool). ((uint b = uint (4 :: 64 word) \<longrightarrow> o2 = True) \<and> (o2 = True \<longrightarrow> b = (4 :: 64 word))) \<and> (if o2 = True then result = (2 :: 32 word) else \<exists>(o3 :: bool). ((uint b = uint (8 :: 64 word) \<longrightarrow> o3 = True) \<and> (o3 = True \<longrightarrow> b = (8 :: 64 word))) \<and> (if o3 = True then result = (3 :: 32 word) else \<exists>(o4 :: bool). ((uint b = uint (16 :: 64 word) \<longrightarrow> o4 = True) \<and> (o4 = True \<longrightarrow> b = (16 :: 64 word))) \<and> (if o4 = True then result = (4 :: 32 word) else \<exists>(o5 :: bool). ((uint b = uint (32 :: 64 word) \<longrightarrow> o5 = True) \<and> (o5 = True \<longrightarrow> b = (32 :: 64 word))) \<and> (if o5 = True then result = (5 :: 32 word) else \<exists>(o6 :: bool). ((uint b = uint (64 :: 64 word) \<longrightarrow> o6 = True) \<and> (o6 = True \<longrightarrow> b = (64 :: 64 word))) \<and> (if o6 = True then result = (6 :: 32 word) else \<exists>(o7 :: bool). ((uint b = uint (128 :: 64 word) \<longrightarrow> o7 = True) \<and> (o7 = True \<longrightarrow> b = (128 :: 64 word))) \<and> (if o7 = True then result = (7 :: 32 word) else \<exists>(o8 :: bool). ((uint b = uint (256 :: 64 word) \<longrightarrow> o8 = True) \<and> (o8 = True \<longrightarrow> b = (256 :: 64 word))) \<and> (if o8 = True then result = (8 :: 32 word) else result = (0 :: 32 word))))))))"
  shows "(0 :: int) \<le> uint result"
  and "uint result \<le> (8 :: int)"
  and "\<not>uint result = (0 :: int) \<longrightarrow> (2 :: int) ^\<^sub>i uint result = uint b"
  and "uint result = (0 :: int) \<longrightarrow> (\<forall>(n :: int). (0 :: int) \<le> n \<longrightarrow> \<not>(2 :: int) ^\<^sub>i n = uint b)"
  sorry
end
