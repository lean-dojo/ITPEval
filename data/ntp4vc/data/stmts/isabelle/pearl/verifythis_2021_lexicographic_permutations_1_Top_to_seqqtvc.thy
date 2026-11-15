theory verifythis_2021_lexicographic_permutations_1_Top_to_seqqtvc
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
theorem to_seq'vc:
  fixes a :: "int list"
  shows "let o1 :: int = int (length a) - (1 :: int) in ((0 :: int) \<le> o1 + (1 :: int) \<longrightarrow> (int (length []) = (0 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (0 :: int) \<longrightarrow> [] ! nat i = a ! (0 :: nat))) \<and> (\<forall>(s :: int list). (((0 :: int) \<le> int (length s) \<and> int (length s) \<le> o1) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> s ! nat i = a ! length s) \<longrightarrow> ((0 :: int) \<le> int (length s) \<and> length s < length a) \<and> (let o2 :: int = a ! length s; o3 :: int list = s @ [o2] in int (length o3) = (1 :: int) + int (length s) \<and> o3 ! length s = o2 \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> o3 ! nat i = s ! nat i) \<longrightarrow> int (length o3) = int (length s) + (1 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) + (1 :: int) \<longrightarrow> o3 ! nat i = a ! nat (int (length s) + (1 :: int))))) \<and> (int (length s) = o1 + (1 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < o1 + (1 :: int) \<longrightarrow> s ! nat i = a ! nat (o1 + (1 :: int))) \<longrightarrow> length s = length a \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> s ! nat i = a ! nat i)))) \<and> (o1 + (1 :: int) < (0 :: int) \<longrightarrow> (let r :: int list = [] in length r = length a \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length r) \<longrightarrow> r ! nat i = a ! nat i)))"
  sorry
end
