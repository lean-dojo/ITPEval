theory queens_NQueensSetsTermination_tqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./queens_S"
begin
theorem t'vc:
  fixes a :: "int FSet.fset"
  fixes o1 :: "int FSet.fset"
  fixes b :: "int FSet.fset"
  fixes o2 :: "int FSet.fset"
  fixes c :: "int FSet.fset"
  assumes fact0: "\<not>a = fempty"
  assumes fact1: "o1 = a |-| b"
  assumes fact2: "o2 = o1 |-| c"
  shows "o2 |\<subseteq>| a |-| b |-| c"
  and "\<forall>(f :: int) (e :: int FSet.fset). e |\<subseteq>| a |-| b |-| c \<longrightarrow> \<not>e = fempty \<longrightarrow> \<not>e = fempty \<and> (let d :: int = Min (fset e) in \<forall>(o3 :: int FSet.fset). o3 = finsert d c \<and> (if d |\<in>| c then fcard o3 = fcard c else int (fcard o3) = int (fcard c) + (1 :: int)) \<longrightarrow> (\<forall>(o4 :: int FSet.fset). (\<forall>(i :: int). i |\<in>| o4 \<longleftrightarrow> (0 :: int) \<le> i \<and> i + (1 :: int) |\<in>| o3) \<longrightarrow> (\<forall>(o5 :: int FSet.fset). o5 = finsert d b \<and> (if d |\<in>| b then fcard o5 = fcard b else int (fcard o5) = int (fcard b) + (1 :: int)) \<longrightarrow> (\<forall>(o6 :: int FSet.fset). (\<forall>(i :: int). i |\<in>| o6 \<longleftrightarrow> (1 :: int) \<le> i \<and> i - (1 :: int) |\<in>| o5) \<longrightarrow> (\<forall>(o7 :: int FSet.fset). o7 = fset_remove d a \<and> (if d |\<in>| a then int (fcard o7) = int (fcard a) - (1 :: int) else fcard o7 = fcard a) \<longrightarrow> ((0 :: int) \<le> int (fcard a) \<and> fcard o7 < fcard a) \<and> (\<forall>(o8 :: int) (o9 :: int FSet.fset). o9 = fset_remove d e \<and> (if d |\<in>| e then int (fcard o9) = int (fcard e) - (1 :: int) else fcard o9 = fcard e) \<longrightarrow> ((0 :: int) \<le> int (fcard e) \<and> fcard o9 < fcard e) \<and> o9 |\<subseteq>| a |-| b |-| c))))))"
  sorry
end
