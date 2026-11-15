theory string_search_BadShiftTable_searchqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./string_search_Spec" "./string_search_Occurs" "Why3STD.ocaml_Exceptions"
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
theorem search'vc:
  fixes bst :: "bad_shift_table"
  fixes "text" :: "string"
  assumes fact0: "length (pat bst) \<le> length text"
  shows "let pat1 :: string = pat bst in \<forall>(m :: 63 word). sint m = int (length pat1) \<and> (0 :: int) \<le> int (length pat1) \<longrightarrow> (\<forall>(n :: 63 word). sint n = int (length text) \<and> (0 :: int) \<le> int (length text) \<longrightarrow> (((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> sint n) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < (0 :: int) \<longrightarrow> j \<le> sint n - sint m \<longrightarrow> \<not>drop (nat j) (take (nat (sint m) - nat j) text) = pat1)) \<and> (\<forall>(i :: 63 word). ((0 :: int) \<le> sint i \<and> sint i \<le> sint n) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < sint i \<longrightarrow> j \<le> sint n - sint m \<longrightarrow> \<not>drop (nat j) (take (nat (sint m) - nat j) text) = pat1) \<longrightarrow> int'63_in_bounds (sint n - sint m) \<and> (\<forall>(o1 :: 63 word). sint o1 = sint n - sint m \<longrightarrow> (if sint i \<le> sint o1 then ((0 :: int) \<le> sint i \<and> sint i \<le> int (length text) - int (length pat1)) \<and> (if matches1 pat1 text (sint i) then (-(1 :: int) \<le> sint i \<and> sint i \<le> int (length text) - int (length (pat bst))) \<and> (if sint i = -(1 :: int) then \<forall>(j :: int). \<not>matches1 (pat bst) text j else matches1 (pat bst) text (sint i)) else int'63_in_bounds (sint n - sint m) \<and> (\<forall>(o2 :: 63 word). sint o2 = sint n - sint m \<longrightarrow> (sint i = sint o2 \<longrightarrow> i = o2) \<longrightarrow> (if i = o2 then (-(1 :: int) \<le> -(1 :: int) \<and> -(1 :: int) \<le> int (length text) - int (length (pat bst))) \<and> (\<forall>(j :: int). \<not>matches1 (pat bst) text j) else int'63_in_bounds (sint i + sint m) \<and> (\<forall>(o3 :: 63 word). sint o3 = sint i + sint m \<longrightarrow> ((0 :: int) \<le> sint o3 \<and> sint o3 < int (length text)) \<and> (let c :: char = text ! nat (sint o3) in (if c |\<in>| fmdom (to_fmap (sht bst)) then c |\<in>| fmdom (to_fmap (sht bst)) else int'63_in_bounds (sint m + (1 :: int))) \<and> (\<forall>(o4 :: 63 word). (if c |\<in>| fmdom (to_fmap (sht bst)) then let o5 :: 63 word t = sht bst in o4 = fm_contents (to_fmap o5) c \<and> o4 = the (fmlookup (to_fmap o5) c) else sint o4 = sint m + (1 :: int)) \<longrightarrow> int'63_in_bounds (sint i + sint o4) \<and> (\<forall>(o5 :: 63 word). sint o5 = sint i + sint o4 \<longrightarrow> ((0 :: int) \<le> sint n - sint m - sint i \<and> sint n - sint m - sint o5 < sint n - sint m - sint i) \<and> ((0 :: int) \<le> sint o5 \<and> sint o5 \<le> sint n) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < sint o5 \<longrightarrow> j \<le> sint n - sint m \<longrightarrow> \<not>drop (nat j) (take (nat (sint m) - nat j) text) = pat1)))))))) else (-(1 :: int) \<le> -(1 :: int) \<and> -(1 :: int) \<le> int (length text) - int (length (pat bst))) \<and> (\<forall>(j :: int). \<not>matches1 (pat bst) text j)))))"
  sorry
end
