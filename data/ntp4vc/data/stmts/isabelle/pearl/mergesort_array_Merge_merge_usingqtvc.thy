theory mergesort_array_Merge_merge_usingqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_MapEq" "Why3STD.map_MapExchange" "Why3STD.map_MapPermut"
begin
typedecl  elt
consts le :: "elt \<Rightarrow> elt \<Rightarrow> bool"
axiomatization where Refl:   "le x x"
  for x :: "elt"
axiomatization where Trans:   "le x z"
 if "le x y"
 and "le y z"
  for x :: "elt"
  and y :: "elt"
  and z :: "elt"
axiomatization where Total:   "le x y \<or> le y x"
  for x :: "elt"
  and y :: "elt"
definition sorted_sub :: "elt list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "sorted_sub a l u \<longleftrightarrow> (\<forall>(i1 :: int) (i2 :: int). l \<le> i1 \<and> i1 < i2 \<and> i2 < u \<longrightarrow> le (a ! nat i1) (a ! nat i2))" for a l u
definition sorted :: "elt list \<Rightarrow> _"
  where "sorted a \<longleftrightarrow> (\<forall>(i1 :: int) (i2 :: int). (0 :: int) \<le> i1 \<and> i1 < i2 \<and> i2 < int (length a) \<longrightarrow> le (a ! nat i1) (a ! nat i2))" for a
theorem merge_using'vc:
  fixes l :: "int"
  fixes m :: "int"
  fixes r :: "int"
  fixes tmp :: "elt list"
  fixes a :: "elt list"
  fixes o1 :: "bool"
  assumes fact0: "(0 :: int) \<le> l"
  assumes fact1: "l \<le> m"
  assumes fact2: "m \<le> r"
  assumes fact3: "r \<le> int (length tmp)"
  assumes fact4: "length tmp = length a"
  assumes fact5: "sorted_sub a l m"
  assumes fact6: "sorted_sub a m r"
  assumes fact7: "if l < m then o1 = (if m < r then True else False) else o1 = False"
  shows "if o1 = True then ((0 :: int) \<le> m \<and> m < int (length a)) \<and> (let o2 :: int = m - (1 :: int) in ((0 :: int) \<le> o2 \<and> o2 < int (length a)) \<and> (if le (a ! nat o2) (a ! nat m) then sorted_sub a l r \<and> permut_sub a a (nat l) (nat r) else let o3 :: int = r - l in (((0 :: int) \<le> l \<and> (0 :: int) \<le> o3 \<and> l + o3 \<le> int (length a)) \<and> (0 :: int) \<le> l \<and> l + o3 \<le> int (length tmp)) \<and> (\<forall>(tmp1 :: elt list). length tmp1 = length tmp \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < l \<or> l + o3 \<le> i \<and> i < int (length tmp1) \<longrightarrow> tmp1 ! nat i = tmp ! nat i) \<and> (\<forall>(i :: int). l \<le> i \<and> i < l + o3 \<longrightarrow> tmp1 ! nat i = a ! nat (l + i - l)) \<longrightarrow> (((0 :: int) \<le> l \<and> l \<le> m \<and> m \<le> r \<and> r \<le> int (length tmp1) \<and> length tmp1 = length a) \<and> sorted_sub tmp1 l m \<and> sorted_sub tmp1 m r) \<and> (\<forall>(a1 :: elt list). length a1 = length a \<longrightarrow> sorted_sub a1 l r \<and> permut_sub tmp1 a1 (nat l) (nat r) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < l \<or> r \<le> i \<and> i < int (length a1) \<longrightarrow> a1 ! nat i = a ! nat i) \<longrightarrow> sorted_sub a1 l r \<and> permut_sub a a1 (nat l) (nat r) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < l \<or> r \<le> i \<and> i < int (length a1) \<longrightarrow> a1 ! nat i = a ! nat i))))) else sorted_sub a l r \<and> permut_sub a a (nat l) (nat r)"
  sorry
end
