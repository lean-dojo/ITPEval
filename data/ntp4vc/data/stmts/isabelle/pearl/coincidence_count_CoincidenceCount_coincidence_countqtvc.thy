theory coincidence_count_CoincidenceCount_coincidence_countqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts mixfix_lbrb_closure :: "'a list \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where mixfix_lbrb_closure_def:   "mixfix_lbrb_closure y y1 = y ! nat y1"
  for y :: "'a list"
  and y1 :: "int"
definition setof :: "'a list \<Rightarrow> 'a fset"
  where "setof a = mixfix_lbrb_closure a |`| Ico_fset_int (0 :: int) (int (length a))" for a
definition drop :: "'a list \<Rightarrow> int \<Rightarrow> 'a fset"
  where "drop a n = mixfix_lbrb_closure a |`| Ico_fset_int n (int (length a))" for a n
definition increasing :: "int list \<Rightarrow> _"
  where "increasing a \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < j \<and> j < int (length a) \<longrightarrow> a ! nat i < a ! nat j)" for a
definition cc :: "int list \<Rightarrow> int list \<Rightarrow> int"
  where "cc a b = int (fcard (setof a |\<inter>| setof b))" for a b
theorem coincidence_count'vc:
  fixes a :: "int list"
  fixes b :: "int list"
  assumes fact0: "increasing a"
  assumes fact1: "increasing b"
  shows "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> int (length a)"
  and "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> int (length b)"
  and "(0 :: int) + int (fcard (drop a (0 :: int) |\<inter>| drop b (0 :: int))) = cc a b"
  and "\<forall>(c :: int) (j :: int) (i :: int). ((0 :: int) \<le> i \<and> i \<le> int (length a)) \<and> ((0 :: int) \<le> j \<and> j \<le> int (length b)) \<and> c + int (fcard (drop a i |\<inter>| drop b j)) = cc a b \<longrightarrow> (\<forall>(o1 :: bool). (if i < int (length a) then o1 = (if j < int (length b) then True else False) else o1 = False) \<longrightarrow> (if o1 = True then ((0 :: int) \<le> j \<and> j < int (length b)) \<and> ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (if a ! nat i < b ! nat j then ((0 :: int) \<le> int (length a) - i + int (length b) - j \<and> int (length a) - (i + (1 :: int)) + int (length b) - j < int (length a) - i + int (length b) - j) \<and> ((0 :: int) \<le> i + (1 :: int) \<and> i + (1 :: int) \<le> int (length a)) \<and> ((0 :: int) \<le> j \<and> j \<le> int (length b)) \<and> c + int (fcard (drop a (i + (1 :: int)) |\<inter>| drop b j)) = cc a b else ((0 :: int) \<le> j \<and> j < int (length b)) \<and> ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (if b ! nat j < a ! nat i then ((0 :: int) \<le> int (length a) - i + int (length b) - j \<and> int (length a) - i + int (length b) - (j + (1 :: int)) < int (length a) - i + int (length b) - j) \<and> ((0 :: int) \<le> i \<and> i \<le> int (length a)) \<and> ((0 :: int) \<le> j + (1 :: int) \<and> j + (1 :: int) \<le> int (length b)) \<and> c + int (fcard (drop a i |\<inter>| drop b (j + (1 :: int)))) = cc a b else ((0 :: int) \<le> int (length a) - i + int (length b) - j \<and> int (length a) - (i + (1 :: int)) + int (length b) - (j + (1 :: int)) < int (length a) - i + int (length b) - j) \<and> ((0 :: int) \<le> i + (1 :: int) \<and> i + (1 :: int) \<le> int (length a)) \<and> ((0 :: int) \<le> j + (1 :: int) \<and> j + (1 :: int) \<le> int (length b)) \<and> c + (1 :: int) + int (fcard (drop a (i + (1 :: int)) |\<inter>| drop b (j + (1 :: int)))) = cc a b)) else c = cc a b))"
  sorry
end
