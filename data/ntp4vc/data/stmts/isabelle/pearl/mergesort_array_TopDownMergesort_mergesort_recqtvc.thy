theory mergesort_array_TopDownMergesort_mergesort_recqtvc
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
theorem mergesort_rec'vc:
  fixes l :: "int"
  fixes r :: "int"
  fixes a :: "elt list"
  fixes tmp :: "elt list"
  assumes fact0: "(0 :: int) \<le> l"
  assumes fact1: "l \<le> r"
  assumes fact2: "r \<le> int (length a)"
  assumes fact3: "length a = length tmp"
  shows "if r - (1 :: int) \<le> l then sorted_sub a l r \<and> permut_sub' a a (nat l) (nat r) else \<not>(2 :: int) = (0 :: int) \<and> (let m :: int = l + (r - l) cdiv (2 :: int) in (((0 :: int) \<le> r - l \<and> m - l < r - l) \<and> (0 :: int) \<le> l \<and> l \<le> m \<and> m \<le> int (length a) \<and> length a = length tmp) \<and> (\<forall>(tmp1 :: elt list) (a1 :: elt list). length tmp1 = length tmp \<longrightarrow> length a1 = length a \<longrightarrow> sorted_sub a1 l m \<and> permut_sub' a a1 (nat l) (nat m) \<longrightarrow> (((0 :: int) \<le> r - l \<and> r - m < r - l) \<and> (0 :: int) \<le> m \<and> m \<le> r \<and> r \<le> int (length a1) \<and> length a1 = length tmp1) \<and> (\<forall>(tmp2 :: elt list) (a2 :: elt list). length tmp2 = length tmp1 \<longrightarrow> length a2 = length a1 \<longrightarrow> sorted_sub a2 m r \<and> permut_sub' a1 a2 (nat m) (nat r) \<longrightarrow> (((0 :: int) \<le> l \<and> l \<le> m \<and> m \<le> r \<and> r \<le> int (length tmp2) \<and> length tmp2 = length a2) \<and> sorted_sub a2 l m \<and> sorted_sub a2 m r) \<and> (\<forall>(a3 :: elt list). length a3 = length a2 \<longrightarrow> sorted_sub a3 l r \<and> permut_sub a2 a3 (nat l) (nat r) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < l \<or> r \<le> i \<and> i < int (length a3) \<longrightarrow> a3 ! nat i = a2 ! nat i) \<longrightarrow> sorted_sub a3 l r \<and> permut_sub' a a3 (nat l) (nat r)))))"
  sorry
end
