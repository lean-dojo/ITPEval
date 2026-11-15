theory sub_SubOld_wmpn_sub_nqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.c_C" "mach.int_Unsigned" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/ptralias_Alias"
begin
theorem wmpn_sub_n'vc:
  fixes x :: "64 word ptr"
  fixes sz :: "32 word"
  fixes y :: "64 word ptr"
  fixes r :: "64 word ptr"
  assumes fact0: "valid x (sint sz)"
  assumes fact1: "valid y (sint sz)"
  assumes fact2: "valid r (sint sz)"
  assumes fact3: "writable r = True"
  shows "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> sint sz"
  and "value r (0 :: int) - ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i (0 :: int) * (0 :: int) = value x (0 :: int) - value y (0 :: int)"
  and "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> (1 :: int)"
  and "\<forall>(i :: 32 word) (b :: 64 word) (r1 :: 64 word ptr). length (data r1) = length (data r) \<and> offset r1 = offset r \<and> c_C.min r1 = c_C.min r \<and> c_C.max r1 = c_C.max r \<and> writable r1 = writable r \<and> zone1 r1 = zone1 r \<longrightarrow> ((0 :: int) \<le> sint i \<and> sint i \<le> sint sz) \<and> value r1 (sint i) - ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i sint i * uint b = value x (sint i) - value y (sint i) \<and> (\<forall>(j :: int). j < offset r1 \<or> offset r1 + sint sz \<le> j \<longrightarrow> pelts r1 j = pelts r j) \<and> (0 :: int) \<le> uint b \<and> uint b \<le> (1 :: int) \<longrightarrow> (if sint i < sint sz then (c_C.min x \<le> offset x + sint i \<and> offset x + sint i < c_C.max x) \<and> (c_C.min y \<le> offset y + sint i \<and> offset y + sint i < c_C.max y) \<and> ((0 :: int) \<le> uint b \<and> uint b \<le> (1 :: int)) \<and> (\<forall>(res :: 64 word) (borrow :: 64 word). uint res - ((18446744073709551615 :: int) + (1 :: int)) * uint borrow = uint (pelts x (offset x + sint i)) - uint (pelts y (offset y + sint i)) - uint b \<and> (0 :: int) \<le> uint borrow \<and> uint borrow \<le> (1 :: int) \<longrightarrow> ((c_C.min r1 \<le> offset r1 + sint i \<and> offset r1 + sint i < c_C.max r1) \<and> writable r1 = True) \<and> (\<forall>(r2 :: 64 word ptr). length (data r2) = length (data r1) \<and> offset r2 = offset r1 \<and> c_C.min r2 = c_C.min r1 \<and> c_C.max r2 = c_C.max r1 \<and> writable r2 = writable r1 \<and> zone1 r2 = zone1 r1 \<longrightarrow> pelts r2 = (pelts r1)(offset r2 + sint i := res) \<and> pelts r2 (offset r2 + sint i) = res \<longrightarrow> int'32_in_bounds (sint i + (1 :: int)) \<and> (\<forall>(o1 :: 32 word). sint o1 = sint i + (1 :: int) \<longrightarrow> ((0 :: int) \<le> sint sz - sint i \<and> sint sz - sint o1 < sint sz - sint i) \<and> ((0 :: int) \<le> sint o1 \<and> sint o1 \<le> sint sz) \<and> value r2 (sint o1) - ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i sint o1 * uint borrow = value x (sint o1) - value y (sint o1) \<and> (\<forall>(j :: int). j < offset r2 \<or> offset r2 + sint sz \<le> j \<longrightarrow> pelts r2 j = pelts r j) \<and> (0 :: int) \<le> uint borrow \<and> uint borrow \<le> (1 :: int)))) else ((0 :: int) \<le> uint b \<and> uint b \<le> (1 :: int)) \<and> value r1 (sint sz) - ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i sint sz * uint b = value x (sint sz) - value y (sint sz) \<and> (\<forall>(j :: int). j < offset r1 \<or> offset r1 + sint sz \<le> j \<longrightarrow> pelts r1 j = pelts r j))"
  sorry
end
