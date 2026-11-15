theory decrease1_Decrease1_searchqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
definition decrease1 :: "int list \<Rightarrow> _"
  where "decrease1 a \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length a) - (1 :: int) \<longrightarrow> a ! nat i - (1 :: int) \<le> a ! nat (i + (1 :: int)))" for a
theorem search'vc:
  fixes a :: "int list"
  assumes fact0: "decrease1 a"
  shows "(0 :: int) \<le> (0 :: int)"
  and "\<forall>(j :: int). (0 :: int) \<le> j \<and> j < (0 :: int) \<longrightarrow> j < int (length a) \<longrightarrow> \<not>a ! nat j = (0 :: int)"
  and "\<forall>(i :: int). (0 :: int) \<le> i \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i \<longrightarrow> j < int (length a) \<longrightarrow> \<not>a ! nat j = (0 :: int)) \<longrightarrow> (if i < int (length a) then ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (if a ! nat i = (0 :: int) then i = -(1 :: int) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < int (length a) \<longrightarrow> \<not>a ! nat j = (0 :: int)) \<or> ((0 :: int) \<le> i \<and> i < int (length a)) \<and> a ! nat i = (0 :: int) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i \<longrightarrow> \<not>a ! nat j = (0 :: int)) else ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (if (0 :: int) < a ! nat i then ((0 :: int) \<le> i \<and> i < int (length a)) \<and> ((0 :: int) \<le> int (length a) - i \<and> int (length a) - (i + a ! nat i) < int (length a) - i) \<and> (0 :: int) \<le> i + a ! nat i \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i + a ! nat i \<longrightarrow> j < int (length a) \<longrightarrow> \<not>a ! nat j = (0 :: int)) else ((0 :: int) \<le> int (length a) - i \<and> int (length a) - (i + (1 :: int)) < int (length a) - i) \<and> (0 :: int) \<le> i + (1 :: int) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i + (1 :: int) \<longrightarrow> j < int (length a) \<longrightarrow> \<not>a ! nat j = (0 :: int)))) else (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < int (length a) \<longrightarrow> \<not>a ! nat j = (0 :: int)) \<or> ((0 :: int) \<le> -(1 :: int) \<and> -(1 :: int) < int (length a)) \<and> a ! nat (-(1 :: int)) = (0 :: int) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < -(1 :: int) \<longrightarrow> \<not>a ! nat j = (0 :: int)))"
  sorry
end
