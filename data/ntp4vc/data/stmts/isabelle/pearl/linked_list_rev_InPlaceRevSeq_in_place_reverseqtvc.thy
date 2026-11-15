theory linked_list_rev_InPlaceRevSeq_in_place_reverseqtvc
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
theorem in_place_reverse'vc:
  fixes next1 :: "loc \<Rightarrow> loc"
  fixes l :: "loc"
  fixes lM :: "loc list"
  assumes fact0: "list_seg next1 l lM null"
  shows "list_seg next1 l lM null"
  and "list_seg next1 null [] null"
  and "disjoint lM []"
  and "rev lM @ [] = rev lM"
  and "\<forall>(rM :: loc list) (r :: loc) (pM :: loc list) (p :: loc) (next2 :: loc \<Rightarrow> loc). list_seg next2 p pM null \<and> list_seg next2 r rM null \<and> disjoint pM rM \<and> rev pM @ rM = rev lM \<longrightarrow> (let o1 :: loc = null; o2 :: bool = eq_loc p o1 in (o2 = True \<longleftrightarrow> p = o1) \<longrightarrow> (if \<not>o2 = True then \<not>p = null \<and> \<not>p = null \<and> (let o3 :: loc = pM ! (0 :: nat); o4 :: loc list = Cons o3 rM in int (length o4) = (1 :: int) + int (length rM) \<and> o4 ! (0 :: nat) = o3 \<and> (\<forall>(i :: int). (0 :: int) < i \<and> i \<le> int (length rM) \<longrightarrow> o4 ! nat i = rM ! nat (i - (1 :: int))) \<longrightarrow> ((0 :: int) \<le> (1 :: int) \<and> (1 :: int) \<le> int (length pM)) \<and> ((0 :: int) \<le> int (length pM) \<and> length (drop (1 :: nat) pM) < length pM) \<and> list_seg (next2(p := r)) (next2 p) (drop (1 :: nat) pM) null \<and> list_seg (next2(p := r)) p o4 null \<and> disjoint (drop (1 :: nat) pM) o4 \<and> rev (drop (1 :: nat) pM) @ o4 = rev lM) else list_seg next2 r (rev lM) null))"
  sorry
end
