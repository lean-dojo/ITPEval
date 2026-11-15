theory coincidence_count_CoincidenceCountBag_coincidence_countqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
definition increasing :: "int list \<Rightarrow> _"
  where "increasing a \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < j \<and> j < int (length a) \<longrightarrow> a ! nat i \<le> a ! nat j)" for a
consts bagofsub :: "'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a multiset"
axiomatization where bagofsub'def:   "if hi \<le> lo then bagofsub a lo hi = ({#} :: 'a multiset) else bagofsub a lo hi = add_mset (a ! nat lo) (bagofsub a (lo + (1 :: int)) hi)"
 if "(0 :: int) \<le> lo"
 and "lo \<le> hi"
 and "hi \<le> int (length a)"
  for lo :: "int"
  and hi :: "int"
  and a :: "'a list"
definition bagof :: "'a list \<Rightarrow> 'a multiset"
  where "bagof a = bagofsub a (0 :: int) (int (length a))" for a
definition drop :: "'a list \<Rightarrow> int \<Rightarrow> 'a multiset"
  where "drop a i = bagofsub a i (int (length a))" for a i
theorem coincidence_count'vc:
  fixes a :: "int list"
  fixes b :: "int list"
  assumes fact0: "increasing a"
  assumes fact1: "increasing b"
  shows "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> int (length a)"
  and "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> int (length b)"
  and "(0 :: int) + int (size (drop a (0 :: int) \<inter># drop b (0 :: int))) = int (size (bagof a \<inter># bagof b))"
  and "\<forall>(c :: int) (j :: int) (i :: int). ((0 :: int) \<le> i \<and> i \<le> int (length a)) \<and> ((0 :: int) \<le> j \<and> j \<le> int (length b)) \<and> c + int (size (drop a i \<inter># drop b j)) = int (size (bagof a \<inter># bagof b)) \<longrightarrow> (\<forall>(o1 :: bool). (if i < int (length a) then o1 = (if j < int (length b) then True else False) else o1 = False) \<longrightarrow> (if o1 = True then ((0 :: int) \<le> j \<and> j < int (length b)) \<and> ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (if a ! nat i < b ! nat j then ((0 :: int) \<le> int (length a) - i + int (length b) - j \<and> int (length a) - (i + (1 :: int)) + int (length b) - j < int (length a) - i + int (length b) - j) \<and> ((0 :: int) \<le> i + (1 :: int) \<and> i + (1 :: int) \<le> int (length a)) \<and> ((0 :: int) \<le> j \<and> j \<le> int (length b)) \<and> c + int (size (drop a (i + (1 :: int)) \<inter># drop b j)) = int (size (bagof a \<inter># bagof b)) else ((0 :: int) \<le> j \<and> j < int (length b)) \<and> ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (if b ! nat j < a ! nat i then ((0 :: int) \<le> int (length a) - i + int (length b) - j \<and> int (length a) - i + int (length b) - (j + (1 :: int)) < int (length a) - i + int (length b) - j) \<and> ((0 :: int) \<le> i \<and> i \<le> int (length a)) \<and> ((0 :: int) \<le> j + (1 :: int) \<and> j + (1 :: int) \<le> int (length b)) \<and> c + int (size (drop a i \<inter># drop b (j + (1 :: int)))) = int (size (bagof a \<inter># bagof b)) else ((0 :: int) \<le> int (length a) - i + int (length b) - j \<and> int (length a) - (i + (1 :: int)) + int (length b) - (j + (1 :: int)) < int (length a) - i + int (length b) - j) \<and> ((0 :: int) \<le> i + (1 :: int) \<and> i + (1 :: int) \<le> int (length a)) \<and> ((0 :: int) \<le> j + (1 :: int) \<and> j + (1 :: int) \<le> int (length b)) \<and> c + (1 :: int) + int (size (drop a (i + (1 :: int)) \<inter># drop b (j + (1 :: int)))) = int (size (bagof a \<inter># bagof b)))) else c = int (size (bagof a \<inter># bagof b))))"
  sorry
end
