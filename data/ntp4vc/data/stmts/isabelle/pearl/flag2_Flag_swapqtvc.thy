theory flag2_Flag_swapqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
datatype  color = Blue | White | Red
definition monochrome :: "(int \<Rightarrow> color) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> color \<Rightarrow> _"
  where "monochrome a i j c \<longleftrightarrow> (\<forall>(k :: int). i \<le> k \<and> k < j \<longrightarrow> a k = c)" for a i j c
consts nb_occ :: "(int \<Rightarrow> color) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> color \<Rightarrow> int"
axiomatization where nb_occ'def:   "if j \<le> i then nb_occ a i j c = (0 :: int) else if a (j - (1 :: int)) = c then nb_occ a i j c = (1 :: int) + nb_occ a i (j - (1 :: int)) c else nb_occ a i j c = nb_occ a i (j - (1 :: int)) c"
  for j :: "int"
  and i :: "int"
  and a :: "int \<Rightarrow> color"
  and c :: "color"
theorem swap'vc:
  fixes i :: "int"
  fixes a :: "color list"
  fixes j :: "int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < int (length a)"
  assumes fact2: "(0 :: int) \<le> j"
  assumes fact3: "j < int (length a)"
  shows "(0 :: int) \<le> i"
  and "i < int (length a)"
  and "let ai :: color = a ! nat i in ((0 :: int) \<le> j \<and> j < int (length a)) \<and> (let aj :: color = a ! nat j in ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (length (a[nat i := aj]) = length a \<longrightarrow> nth (a[nat i := aj]) o nat = (nth a o nat)(i := aj) \<longrightarrow> ((0 :: int) \<le> j \<and> j < int (length (a[nat i := aj]))) \<and> (length (a[nat j := ai, nat i := aj]) = length (a[nat i := aj]) \<longrightarrow> nth (a[nat j := ai, nat i := aj]) o nat = (nth (a[nat i := aj]) o nat)(j := ai) \<longrightarrow> a[nat j := ai, nat i := aj] ! nat i = a ! nat j \<and> a[nat j := ai, nat i := aj] ! nat j = a ! nat i \<and> (\<forall>(k :: int). \<not>k = i \<and> \<not>k = j \<longrightarrow> a[nat j := ai, nat i := aj] ! nat k = a ! nat k) \<and> (\<forall>(k1 :: int) (k2 :: int) (c :: color). (k1 \<le> i \<and> i < k2) \<and> k1 \<le> j \<and> j < k2 \<longrightarrow> nb_occ (nth (a[nat j := ai, nat i := aj]) o nat) k1 k2 c = nb_occ (nth a o nat) k1 k2 c))))"
  sorry
end
