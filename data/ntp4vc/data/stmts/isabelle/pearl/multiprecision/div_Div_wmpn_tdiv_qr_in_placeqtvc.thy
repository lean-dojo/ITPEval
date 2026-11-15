theory div_Div_wmpn_tdiv_qr_in_placeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/compare_Compare" "../../lib/isabelle/util_Util" "../../lib/isabelle/ptralias_Alias" "../../lib/isabelle/util_UtilOld" "../../lib/isabelle/add_Add" "../../lib/isabelle/add_AddOld" "../../lib/isabelle/sub_SubOld" "../../lib/isabelle/logical_LogicalUtil" "../../lib/isabelle/logical_LogicalOld" "../../lib/isabelle/mul_Mul"
begin
definition reciprocal :: "64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal v d \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv uint d - ((18446744073709551615 :: int) + (1 :: int))" for v d
definition reciprocal_3by2 :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal_3by2 v dh dl \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv (uint dl + ((18446744073709551615 :: int) + (1 :: int)) * uint dh) - ((18446744073709551615 :: int) + (1 :: int))" for v dh dl
definition normalized :: "64 word ptr \<Rightarrow> 32 word \<Rightarrow> _"
  where "normalized x sz \<longleftrightarrow> valid x (sint sz) \<and> ((18446744073709551615 :: int) + (1 :: int)) ediv (2 :: int) \<le> uint (pelts x (offset x + sint sz - (1 :: int)))" for x sz
theorem wmpn_tdiv_qr_in_place'vc:
  fixes sy :: "32 word"
  fixes sx :: "32 word"
  fixes x :: "64 word ptr"
  fixes y :: "64 word ptr"
  fixes q :: "64 word ptr"
  fixes qxn :: "32 word"
  assumes fact0: "(1 :: int) \<le> sint sy"
  assumes fact1: "sint sy \<le> sint sx"
  assumes fact2: "sint sx \<le> (2147483647 :: int) - (1 :: int)"
  assumes fact3: "valid x (sint sx)"
  assumes fact4: "valid y (sint sy)"
  assumes fact5: "valid q (sint sx - sint sy + (1 :: int))"
  assumes fact6: "writable x = True"
  assumes fact7: "writable q = True"
  assumes fact8: "sint qxn = (0 :: int)"
  assumes fact9: "(0 :: int) < uint (pelts y (offset y + sint sy - (1 :: int)))"
  shows "(0 :: int) \<le> sint sx"
  and "\<forall>(o1 :: 32 word). uint o1 = sint sx \<longrightarrow> uint'32_in_bounds (uint o1 + (1 :: int)) \<and> (\<forall>(o2 :: 32 word). uint o2 = uint o1 + (1 :: int) \<longrightarrow> (0 :: int) \<le> uint o2 \<and> (\<forall>(nx :: 64 word ptr). (\<not>zone1 nx = null_zone \<longrightarrow> plength nx = uint o2) \<and> offset nx = (0 :: int) \<and> c_C.min nx = (0 :: int) \<and> c_C.max nx = plength nx \<and> writable nx = True \<longrightarrow> (is_not_null nx \<longleftrightarrow> \<not>zone1 nx = null_zone) \<longrightarrow> is_not_null nx \<longrightarrow> (0 :: int) \<le> sint sy \<and> (\<forall>(o3 :: 32 word). uint o3 = sint sy \<longrightarrow> (0 :: int) \<le> uint o3 \<and> (\<forall>(ny :: 64 word ptr). (\<not>zone1 ny = null_zone \<longrightarrow> plength ny = uint o3) \<and> offset ny = (0 :: int) \<and> c_C.min ny = (0 :: int) \<and> c_C.max ny = plength ny \<and> writable ny = True \<longrightarrow> (is_not_null ny \<longleftrightarrow> \<not>zone1 ny = null_zone) \<longrightarrow> is_not_null ny \<longrightarrow> (((1 :: int) \<le> sint sy \<and> sint sy \<le> sint sx \<and> sint sx \<le> (2147483647 :: int) - (1 :: int)) \<and> valid x (sint sx) \<and> valid y (sint sy) \<and> valid q (sint sx - sint sy + (1 :: int)) \<and> valid nx (sint sx + (1 :: int)) \<and> valid ny (sint sy) \<and> (writable q = True \<and> writable x = True) \<and> (writable nx = True \<and> writable ny = True) \<and> (0 :: int) < uint (pelts y (offset y + sint sy - (1 :: int)))) \<and> (\<forall>(ny1 :: 64 word ptr) (nx1 :: 64 word ptr) (x1 :: 64 word ptr) (q1 :: 64 word ptr). length (data ny1) = length (data ny) \<and> offset ny1 = offset ny \<and> c_C.min ny1 = c_C.min ny \<and> c_C.max ny1 = c_C.max ny \<and> writable ny1 = writable ny \<and> zone1 ny1 = zone1 ny \<longrightarrow> length (data nx1) = length (data nx) \<and> offset nx1 = offset nx \<and> c_C.min nx1 = c_C.min nx \<and> c_C.max nx1 = c_C.max nx \<and> writable nx1 = writable nx \<and> zone1 nx1 = zone1 nx \<longrightarrow> length (data x1) = length (data x) \<and> offset x1 = offset x \<and> c_C.min x1 = c_C.min x \<and> c_C.max x1 = c_C.max x \<and> writable x1 = writable x \<and> zone1 x1 = zone1 x \<longrightarrow> length (data q1) = length (data q) \<and> offset q1 = offset q \<and> c_C.min q1 = c_C.min q \<and> c_C.max q1 = c_C.max q \<and> writable q1 = writable q \<and> zone1 q1 = zone1 q \<longrightarrow> value x (sint sx) = value q1 (sint sx - sint sy + (1 :: int)) * value y (sint sy) + value x1 (sint sy) \<and> value x1 (sint sy) < value y (sint sy) \<longrightarrow> (offset nx1 = (0 :: int) \<and> c_C.min nx1 = (0 :: int) \<and> c_C.max nx1 = plength nx1 \<and> writable nx1 = True) \<and> (offset ny1 = (0 :: int) \<and> c_C.min ny1 = (0 :: int) \<and> c_C.max ny1 = plength ny1 \<and> writable ny1 = True) \<and> value x (sint sx) = value q1 (sint sx - sint sy + (1 :: int)) * value y (sint sy) + value x1 (sint sy) \<and> value x1 (sint sy) < value y (sint sy))))))"
  sorry
end
