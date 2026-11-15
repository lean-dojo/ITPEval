theory linked_list_rev_InPlaceRevSeq_appqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts result :: "'a list \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where result'def:   "result s i = s ! nat (int (length s) - (1 :: int) - i)"
  for s :: "'a list"
  and i :: "int"
typedecl  loc
consts null :: "loc"
consts eq_loc :: "loc \<Rightarrow> loc \<Rightarrow> bool"
axiomatization where eq_loc'spec:   "eq_loc l1 l2 = True \<longleftrightarrow> l1 = l2"
  for l1 :: "loc"
  and l2 :: "loc"
definition disjoint :: "'a list \<Rightarrow> 'a list \<Rightarrow> _"
  where "disjoint s1 s2 \<longleftrightarrow> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < int (length s1) \<longrightarrow> (\<forall>(i2 :: int). (0 :: int) \<le> i2 \<and> i2 < int (length s2) \<longrightarrow> \<not>s1 ! nat i1 = s2 ! nat i2))" for s1 s2
definition no_repet :: "loc list \<Rightarrow> _"
  where "no_repet s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> \<not>s ! nat i \<in> set (drop (nat (i + (1 :: int))) s))" for s
typedecl 'a memory
typedecl  "next"
definition list_seg :: "(loc \<Rightarrow> loc) \<Rightarrow> loc \<Rightarrow> loc list \<Rightarrow> loc \<Rightarrow> _"
  where "list_seg next1 p s q \<longleftrightarrow> (let n :: int = int (length s) in (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> \<not>s ! nat i = null) \<and> (p = q \<and> n = (0 :: int) \<or> (1 :: int) \<le> n \<and> s ! (0 :: nat) = p \<and> next1 (s ! nat (n - (1 :: int))) = q \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n - (1 :: int) \<longrightarrow> next1 (s ! nat i) = s ! nat (i + (1 :: int)))))" for next1 p s q
theorem app'vc:
  fixes next1 :: "loc \<Rightarrow> loc"
  fixes l1 :: "loc"
  fixes l1M :: "loc list"
  fixes l2 :: "loc"
  fixes l2M :: "loc list"
  assumes fact0: "list_seg next1 l1 l1M null"
  assumes fact1: "list_seg next1 l2 l2M null"
  assumes fact2: "disjoint l1M l2M"
  shows "let o1 :: loc = null; o2 :: bool = eq_loc l1 o1 in (o2 = True \<longleftrightarrow> l1 = o1) \<longrightarrow> (if o2 = True then list_seg next1 l2 (l1M @ l2M) null else (\<not>l1 = null \<and> list_seg next1 l1 [] l1 \<and> list_seg next1 l1 l1M null \<and> [] @ l1M = l1M \<and> disjoint [] l1M) \<and> (\<forall>(l1pM :: loc list) (pM :: loc list) (p :: loc). \<not>p = null \<and> list_seg next1 l1 l1pM p \<and> list_seg next1 p pM null \<and> l1pM @ pM = l1M \<and> disjoint l1pM pM \<longrightarrow> (let o3 :: loc = null in \<not>p = null \<and> (let o4 :: loc = next1 p; o5 :: bool = eq_loc o4 o3 in (o5 = True \<longleftrightarrow> o4 = o3) \<longrightarrow> (if \<not>o5 = True then ((0 :: int) \<le> (1 :: int) \<and> (1 :: int) \<le> int (length pM)) \<and> (let o6 :: loc list = []; o7 :: loc list = Cons p o6 in int (length o7) = (1 :: int) + int (length o6) \<and> o7 ! (0 :: nat) = p \<and> (\<forall>(i :: int). (0 :: int) < i \<and> i \<le> int (length o6) \<longrightarrow> o7 ! nat i = o6 ! nat (i - (1 :: int))) \<longrightarrow> (let o8 :: loc list = l1pM @ o7 in int (length o8) = int (length l1pM) + int (length o7) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length l1pM) \<longrightarrow> o8 ! nat i = l1pM ! nat i) \<and> (\<forall>(i :: int). int (length l1pM) \<le> i \<and> i < int (length o8) \<longrightarrow> o8 ! nat i = o7 ! nat (i - int (length l1pM))) \<longrightarrow> \<not>p = null \<and> ((0 :: int) \<le> int (length pM) \<and> length (drop (1 :: nat) pM) < length pM) \<and> \<not>next1 p = null \<and> list_seg next1 l1 o8 (next1 p) \<and> list_seg next1 (next1 p) (drop (1 :: nat) pM) null \<and> o8 @ drop (1 :: nat) pM = l1M \<and> disjoint o8 (drop (1 :: nat) pM))) else \<not>p = null \<and> list_seg (next1(p := l2)) l1 (l1M @ l2M) null)))))"
  sorry
end
