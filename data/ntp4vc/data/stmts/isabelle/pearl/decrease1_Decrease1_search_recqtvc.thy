theory decrease1_Decrease1_search_recqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
definition decrease1 :: "int list \<Rightarrow> _"
  where "decrease1 a \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length a) - (1 :: int) \<longrightarrow> a ! nat i - (1 :: int) \<le> a ! nat (i + (1 :: int)))" for a
theorem search_rec'vc:
  fixes a :: "int list"
  fixes i :: "int"
  assumes fact0: "decrease1 a"
  assumes fact1: "(0 :: int) \<le> i"
  shows "let o1 :: int = int (length a) in (i < o1 \<longrightarrow> ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (\<not>a ! nat i = (0 :: int) \<longrightarrow> ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (if (0 :: int) < a ! nat i then ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (let o2 :: int = i + a ! nat i in ((0 :: int) \<le> int (length a) - i \<and> int (length a) - o2 < int (length a) - i) \<and> decrease1 a \<and> (0 :: int) \<le> o2) else let o2 :: int = i + (1 :: int) in ((0 :: int) \<le> int (length a) - i \<and> int (length a) - o2 < int (length a) - i) \<and> decrease1 a \<and> (0 :: int) \<le> o2))) \<and> (\<forall>(result :: int). (if i < o1 then if a ! nat i = (0 :: int) then result = i else if (0 :: int) < a ! nat i then let o2 :: int = i + a ! nat i in result = -(1 :: int) \<and> (\<forall>(j :: int). o2 \<le> j \<and> j < int (length a) \<longrightarrow> \<not>a ! nat j = (0 :: int)) \<or> (o2 \<le> result \<and> result < int (length a)) \<and> a ! nat result = (0 :: int) \<and> (\<forall>(j :: int). o2 \<le> j \<and> j < result \<longrightarrow> \<not>a ! nat j = (0 :: int)) else let o2 :: int = i + (1 :: int) in result = -(1 :: int) \<and> (\<forall>(j :: int). o2 \<le> j \<and> j < int (length a) \<longrightarrow> \<not>a ! nat j = (0 :: int)) \<or> (o2 \<le> result \<and> result < int (length a)) \<and> a ! nat result = (0 :: int) \<and> (\<forall>(j :: int). o2 \<le> j \<and> j < result \<longrightarrow> \<not>a ! nat j = (0 :: int)) else result = -(1 :: int)) \<longrightarrow> result = -(1 :: int) \<and> (\<forall>(j :: int). i \<le> j \<and> j < int (length a) \<longrightarrow> \<not>a ! nat j = (0 :: int)) \<or> (i \<le> result \<and> result < int (length a)) \<and> a ! nat result = (0 :: int) \<and> (\<forall>(j :: int). i \<le> j \<and> j < result \<longrightarrow> \<not>a ! nat j = (0 :: int)))"
  sorry
end
