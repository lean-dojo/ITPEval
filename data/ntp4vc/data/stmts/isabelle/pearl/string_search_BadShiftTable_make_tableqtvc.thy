theory string_search_BadShiftTable_make_tableqtvc
  imports "NTP4Verif.NTP4Verif" "./string_search_Spec" "./string_search_Occurs" "Why3STD.ocaml_Exceptions"
begin
typedecl 'v t
consts to_fmap :: "'v t \<Rightarrow> (char, 'v) fmap"
typedecl  bad_shift_table
consts pat :: "bad_shift_table \<Rightarrow> string"
consts sht :: "bad_shift_table \<Rightarrow> 63 word t"
axiomatization where bad_shift_table'invariant'0:   "\<forall>(j :: int) (c :: char). (0 :: int) \<le> j \<and> j < int (length (pat self)) \<longrightarrow> c = pat self ! nat j \<longrightarrow> c |\<in>| fmdom (to_fmap (sht self))"
  for self :: "bad_shift_table"
axiomatization where bad_shift_table'invariant'1:   "\<forall>(c :: char). c |\<in>| fmdom (to_fmap (sht self)) \<longrightarrow> (1 :: int) \<le> sint (fm_contents (to_fmap (sht self)) c) \<and> sint (fm_contents (to_fmap (sht self)) c) \<le> int (length (pat self)) + (1 :: int)"
  for self :: "bad_shift_table"
axiomatization where bad_shift_table'invariant'2:   "\<forall>(c :: char). c |\<in>| fmdom (to_fmap (sht self)) \<longrightarrow> (\<forall>(j :: int). (1 :: int) \<le> j \<and> j < sint (fm_contents (to_fmap (sht self)) c) \<longrightarrow> \<not>pat self ! nat (int (length (pat self)) - j) = c)"
  for self :: "bad_shift_table"
definition bad_shift_table'eq :: "bad_shift_table \<Rightarrow> bad_shift_table \<Rightarrow> _"
  where "bad_shift_table'eq a b \<longleftrightarrow> pat a = pat b \<and> sht a = sht b" for a b
axiomatization where bad_shift_table'inj:   "a = b"
 if "bad_shift_table'eq a b"
  for a :: "bad_shift_table"
  and b :: "bad_shift_table"
theorem make_table'vc:
  fixes m :: "63 word"
  fixes pat1 :: "string"
  fixes sht1 :: "63 word t"
  assumes fact0: "sint m = int (length pat1)"
  assumes fact1: "(0 :: int) \<le> int (length pat1)"
  assumes fact2: "to_fmap sht1 = fmempty"
  shows "int'63_in_bounds (sint m - (1 :: int))"
  and "\<forall>(o1 :: 63 word). sint o1 = sint m - (1 :: int) \<longrightarrow> ((0 :: int) \<le> sint o1 + (1 :: int) \<longrightarrow> ((\<forall>(j :: int). (0 :: int) \<le> j \<and> j < (0 :: int) \<longrightarrow> pat1 ! nat j |\<in>| fmdom (to_fmap sht1)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht1) \<longrightarrow> (1 :: int) \<le> sint (fm_contents (to_fmap sht1) c) \<and> sint (fm_contents (to_fmap sht1) c) \<le> sint m + (1 :: int)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht1) \<longrightarrow> (\<forall>(j :: int). sint m - sint (fm_contents (to_fmap sht1) c) < j \<and> j < (0 :: int) \<longrightarrow> \<not>pat1 ! nat j = c))) \<and> (\<forall>(sht2 :: 63 word t). (\<forall>(i :: 63 word). let i1 :: int = sint i in ((0 :: int) \<le> i1 \<and> i1 \<le> sint o1) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i1 \<longrightarrow> pat1 ! nat j |\<in>| fmdom (to_fmap sht2)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht2) \<longrightarrow> (1 :: int) \<le> sint (fm_contents (to_fmap sht2) c) \<and> sint (fm_contents (to_fmap sht2) c) \<le> sint m + (1 :: int)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht2) \<longrightarrow> (\<forall>(j :: int). sint m - sint (fm_contents (to_fmap sht2) c) < j \<and> j < i1 \<longrightarrow> \<not>pat1 ! nat j = c)) \<longrightarrow> int'63_in_bounds (sint m - sint i) \<and> (\<forall>(o2 :: 63 word). sint o2 = sint m - sint i \<longrightarrow> ((0 :: int) \<le> sint i \<and> sint i < int (length pat1)) \<and> (\<forall>(sht3 :: 63 word t). to_fmap sht3 = fmupd (pat1 ! nat (sint i)) o2 (to_fmap sht2) \<longrightarrow> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i1 + (1 :: int) \<longrightarrow> pat1 ! nat j |\<in>| fmdom (to_fmap sht3)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht3) \<longrightarrow> (1 :: int) \<le> sint (fm_contents (to_fmap sht3) c) \<and> sint (fm_contents (to_fmap sht3) c) \<le> sint m + (1 :: int)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht3) \<longrightarrow> (\<forall>(j :: int). sint m - sint (fm_contents (to_fmap sht3) c) < j \<and> j < i1 + (1 :: int) \<longrightarrow> \<not>pat1 ! nat j = c))))) \<and> ((\<forall>(j :: int). (0 :: int) \<le> j \<and> j < sint o1 + (1 :: int) \<longrightarrow> pat1 ! nat j |\<in>| fmdom (to_fmap sht2)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht2) \<longrightarrow> (1 :: int) \<le> sint (fm_contents (to_fmap sht2) c) \<and> sint (fm_contents (to_fmap sht2) c) \<le> sint m + (1 :: int)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht2) \<longrightarrow> (\<forall>(j :: int). sint m - sint (fm_contents (to_fmap sht2) c) < j \<and> j < sint o1 + (1 :: int) \<longrightarrow> \<not>pat1 ! nat j = c)) \<longrightarrow> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < int (length pat1) \<longrightarrow> pat1 ! nat j |\<in>| fmdom (to_fmap sht2)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht2) \<longrightarrow> (1 :: int) \<le> sint (fm_contents (to_fmap sht2) c) \<and> sint (fm_contents (to_fmap sht2) c) \<le> int (length pat1) + (1 :: int)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht2) \<longrightarrow> (\<forall>(j :: int). (1 :: int) \<le> j \<and> j < sint (fm_contents (to_fmap sht2) c) \<longrightarrow> \<not>pat1 ! nat (int (length pat1) - j) = c))))) \<and> (sint o1 + (1 :: int) < (0 :: int) \<longrightarrow> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < int (length pat1) \<longrightarrow> pat1 ! nat j |\<in>| fmdom (to_fmap sht1)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht1) \<longrightarrow> (1 :: int) \<le> sint (fm_contents (to_fmap sht1) c) \<and> sint (fm_contents (to_fmap sht1) c) \<le> int (length pat1) + (1 :: int)) \<and> (\<forall>(c :: char). c |\<in>| fmdom (to_fmap sht1) \<longrightarrow> (\<forall>(j :: int). (1 :: int) \<le> j \<and> j < sint (fm_contents (to_fmap sht1) c) \<longrightarrow> \<not>pat1 ! nat (int (length pat1) - j) = c)))"
  sorry
end
