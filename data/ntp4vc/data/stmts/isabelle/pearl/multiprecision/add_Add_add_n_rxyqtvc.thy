theory add_Add_add_n_rxyqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.c_C" "mach.int_Unsigned" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/ptralias_Alias"
begin
theorem add_n_rxy'vc:
  fixes sx :: "32 word"
  fixes x :: "64 word ptr"
  assumes fact0: "(0 :: int) \<le> sint sx"
  assumes fact1: "writable x = True"
  assumes fact2: "valid x (sint sx)"
  shows "(0 :: int) \<le> sint sx"
  and "valid x (sint sx)"
  and "writable x = True"
  and "\<forall>(x1 :: 64 word ptr). length (data x1) = length (data x) \<and> offset x1 = offset x \<and> c_C.min x1 = c_C.min x \<and> c_C.max x1 = c_C.max x \<and> writable x1 = writable x \<and> zone1 x1 = zone1 x \<longrightarrow> (\<forall>(result :: 64 word). value x1 (sint sx) + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i sint sx * uint result = value x (sint sx) + value x (sint sx) \<and> ((0 :: int) \<le> uint result \<and> uint result \<le> (1 :: int)) \<and> (\<forall>(j :: int). j < offset x1 \<or> offset x1 + sint sx \<le> j \<longrightarrow> pelts x1 j = pelts x j) \<longrightarrow> value x1 (sint sx) + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i sint sx * uint result = value x (sint sx) + value x (sint sx) \<and> ((0 :: int) \<le> uint result \<and> uint result \<le> (1 :: int)) \<and> (\<forall>(j :: int). j < offset x1 \<or> offset x1 + sint sx \<le> j \<longrightarrow> pelts x1 j = pelts x j) \<and> c_C.min x1 = c_C.min x \<and> c_C.max x1 = c_C.max x \<and> plength x1 = plength x)"
  sorry
end
