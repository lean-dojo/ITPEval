theory verifythis_2021_lexicographic_permutations_1_Top_swapqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf"
begin
typedecl  elt
typedecl  permutation
definition lt :: "int list \<Rightarrow> int list \<Rightarrow> _"
  where "lt p q \<longleftrightarrow> (length p = length q \<and> (0 :: int) < int (length q)) \<and> (\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length p)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i \<longrightarrow> p ! nat j = q ! nat j) \<and> p ! nat i < q ! nat i)" for p q
consts iseq :: "'a \<Rightarrow> 'a list \<Rightarrow> int \<Rightarrow> bool"
axiomatization where iseq'def:   "iseq x s i = True \<longleftrightarrow> s ! nat i = x"
  for x :: "'a"
  and s :: "'a list"
  and i :: "int"
definition occ :: "'a \<Rightarrow> 'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "occ x s l u = numof (iseq x s) l u" for x s l u
definition occ_all :: "'a \<Rightarrow> 'a list \<Rightarrow> int"
  where "occ_all x s = occ x s (0 :: int) (int (length s))" for x s
definition is_permutation_of :: "int list \<Rightarrow> int list \<Rightarrow> _"
  where "is_permutation_of p a \<longleftrightarrow> length p = length a \<and> (\<forall>(x :: int). occ_all x p = occ_all x a)" for p a
definition descending :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "descending s lo hi \<longleftrightarrow> ((0 :: int) \<le> lo \<and> lo \<le> hi \<and> hi \<le> int (length s)) \<and> (\<forall>(i :: int) (j :: int). lo \<le> i \<and> i \<le> j \<and> j < hi \<longrightarrow> s ! nat j \<le> s ! nat i)" for s lo hi
definition ascending :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "ascending s lo hi \<longleftrightarrow> ((0 :: int) \<le> lo \<and> lo \<le> hi \<and> hi \<le> int (length s)) \<and> (\<forall>(i :: int) (j :: int). lo \<le> i \<and> i \<le> j \<and> j < hi \<longrightarrow> s ! nat i \<le> s ! nat j)" for s lo hi
consts to_seq :: "int list \<Rightarrow> int list"
axiomatization where to_seq'spec'0:   "length (to_seq a) = length a"
  for a :: "int list"
axiomatization where to_seq'spec:   "to_seq a ! nat i = a ! nat i"
 if "(0 :: int) \<le> i"
 and "i < int (length (to_seq a))"
  for i :: "int"
  and a :: "int list"
theorem swap'vc:
  fixes i :: "int"
  fixes a :: "int list"
  fixes j :: "int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < int (length a)"
  assumes fact2: "(0 :: int) \<le> j"
  assumes fact3: "j < int (length a)"
  shows "(0 :: int) \<le> i"
  and "i < int (length a)"
  and "let temp :: int = a ! nat i in ((0 :: int) \<le> j \<and> j < int (length a)) \<and> (let o1 :: int = a ! nat j in ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (length (a[nat i := o1]) = length a \<longrightarrow> nth (a[nat i := o1]) o nat = (nth a o nat)(i := o1) \<longrightarrow> ((0 :: int) \<le> j \<and> j < int (length (a[nat i := o1]))) \<and> (length (a[nat j := temp, nat i := o1]) = length (a[nat i := o1]) \<longrightarrow> nth (a[nat j := temp, nat i := o1]) o nat = (nth (a[nat i := o1]) o nat)(j := temp) \<longrightarrow> a[nat j := temp, nat i := o1] ! nat i = a ! nat j \<and> a[nat j := temp, nat i := o1] ! nat j = a ! nat i \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length (a[nat j := temp, nat i := o1])) \<longrightarrow> \<not>k = i \<longrightarrow> \<not>k = j \<longrightarrow> a[nat j := temp, nat i := o1] ! nat k = a ! nat k) \<and> is_permutation_of (to_seq (a[nat j := temp, nat i := o1])) (to_seq a))))"
  sorry
end
