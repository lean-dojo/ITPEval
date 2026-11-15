theory compare_Compare_wmpn_cmpqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/lemmas_Lemmas"
begin
definition compare_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where "compare_int x y = (if x < y then -(1 :: int) else if x = y then 0 :: int else (1 :: int))" for x y
theorem wmpn_cmp'vc:
  fixes x :: "64 word ptr"
  fixes sz :: "32 word"
  fixes y :: "64 word ptr"
  assumes fact0: "valid x (sint sz)"
  assumes fact1: "valid y (sint sz)"
  shows "(0 :: int) \<le> sint sz"
  and "sint sz \<le> sint sz"
  and "\<forall>(j :: int). sint sz \<le> j \<and> j < sint sz \<longrightarrow> pelts x (offset x + j) = pelts y (offset y + j)"
  and "\<forall>(i :: 32 word). ((0 :: int) \<le> sint i \<and> sint i \<le> sint sz) \<and> (\<forall>(j :: int). sint i \<le> j \<and> j < sint sz \<longrightarrow> pelts x (offset x + j) = pelts y (offset y + j)) \<longrightarrow> (if (1 :: int) \<le> sint i then int'32_in_bounds (sint i - (1 :: int)) \<and> (\<forall>(o1 :: 32 word). sint o1 = sint i - (1 :: int) \<longrightarrow> (c_C.min x \<le> offset x + sint o1 \<and> offset x + sint o1 < c_C.max x) \<and> (let lx :: 64 word = pelts x (offset x + sint o1) in (c_C.min y \<le> offset y + sint o1 \<and> offset y + sint o1 < c_C.max y) \<and> (let ly :: 64 word = pelts y (offset y + sint o1) in \<forall>(o2 :: bool). (uint lx = uint ly \<longrightarrow> o2 = True) \<and> (o2 = True \<longrightarrow> lx = ly) \<longrightarrow> (if \<not>o2 = True then if uint ly < uint lx then (1 :: int) = compare_int (value x (sint sz)) (value y (sint sz)) else -(1 :: int) = compare_int (value x (sint sz)) (value y (sint sz)) else sint o1 < sint i \<and> ((0 :: int) \<le> sint o1 \<and> sint o1 \<le> sint sz) \<and> (\<forall>(j :: int). sint o1 \<le> j \<and> j < sint sz \<longrightarrow> pelts x (offset x + j) = pelts y (offset y + j)))))) else (0 :: int) = compare_int (value x (sint sz)) (value y (sint sz)))"
  sorry
end
