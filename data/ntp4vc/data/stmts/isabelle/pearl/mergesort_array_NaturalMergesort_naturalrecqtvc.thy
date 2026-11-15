theory mergesort_array_NaturalMergesort_naturalrecqtvc
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
theorem naturalrec'vc:
  fixes lo :: "int"
  fixes a :: "elt list"
  fixes tmp :: "elt list"
  fixes k :: "int"
  assumes fact0: "(0 :: int) \<le> lo"
  assumes fact1: "lo \<le> int (length a)"
  assumes fact2: "length a = length tmp"
  assumes fact3: "(0 :: int) \<le> k"
  shows "let n :: int = int (length a) in if n - (1 :: int) \<le> lo then (n = int (length a) \<or> lo + k < n \<and> n < int (length a)) \<and> sorted_sub a lo n \<and> permut_sub' a a (nat lo) (length a) else ((0 :: int) \<le> lo \<and> lo < int (length a)) \<and> (\<forall>(o1 :: int). (lo < o1 \<and> o1 \<le> int (length a)) \<and> sorted_sub a lo o1 \<and> (o1 < int (length a) \<longrightarrow> \<not>le (a ! nat (o1 - (1 :: int))) (a ! nat o1)) \<longrightarrow> (if o1 = n then (n = int (length a) \<or> lo + k < n \<and> n < int (length a)) \<and> sorted_sub a lo n \<and> permut_sub' a a (nat lo) (length a) else let o2 :: int = k - (1 :: int) in ((0 :: int) \<le> o2 + (1 :: int) \<longrightarrow> ((lo + (0 :: int) < o1 \<and> o1 < n) \<and> sorted_sub a lo o1 \<and> permut_sub' a a (nat lo) (length a)) \<and> (\<forall>(mid :: int) (a1 :: elt list) (tmp1 :: elt list). length a1 = length a \<longrightarrow> length tmp1 = length tmp \<longrightarrow> (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i \<le> o2) \<and> (lo + i < mid \<and> mid < n) \<and> sorted_sub a1 lo mid \<and> permut_sub' a a1 (nat lo) (length a1) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < lo \<longrightarrow> a1 ! nat j = a ! nat j) \<longrightarrow> (((0 :: int) \<le> k \<and> i < k) \<and> ((0 :: int) \<le> mid \<and> mid \<le> int (length a1) \<and> length a1 = length tmp1) \<and> (0 :: int) \<le> i) \<and> (\<forall>(a2 :: elt list) (tmp2 :: elt list). length a2 = length a1 \<longrightarrow> length tmp2 = length tmp1 \<longrightarrow> (\<forall>(hi :: int). (hi = int (length a2) \<or> mid + i < hi \<and> hi < int (length a2)) \<and> sorted_sub a2 mid hi \<and> permut_sub' a1 a2 (nat mid) (length a2) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < mid \<longrightarrow> a2 ! nat j = a1 ! nat j) \<longrightarrow> (((0 :: int) \<le> lo \<and> lo \<le> mid \<and> mid \<le> hi \<and> hi \<le> int (length tmp2) \<and> length tmp2 = length a2) \<and> sorted_sub a2 lo mid \<and> sorted_sub a2 mid hi) \<and> (\<forall>(a3 :: elt list). length a3 = length a2 \<longrightarrow> sorted_sub a3 lo hi \<and> permut_sub a2 a3 (nat lo) (nat hi) \<and> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < lo \<or> hi \<le> i1 \<and> i1 < int (length a3) \<longrightarrow> a3 ! nat i1 = a2 ! nat i1) \<longrightarrow> (if hi = n then (n = int (length a3) \<or> lo + k < n \<and> n < int (length a3)) \<and> sorted_sub a3 lo n \<and> permut_sub' a a3 (nat lo) (length a3) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < lo \<longrightarrow> a3 ! nat j = a ! nat j) else (lo + (i + (1 :: int)) < hi \<and> hi < n) \<and> sorted_sub a3 lo hi \<and> permut_sub' a a3 (nat lo) (length a3) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < lo \<longrightarrow> a3 ! nat j = a ! nat j)))))) \<and> ((lo + (o2 + (1 :: int)) < mid \<and> mid < n) \<and> sorted_sub a1 lo mid \<and> permut_sub' a a1 (nat lo) (length a1) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < lo \<longrightarrow> a1 ! nat j = a ! nat j) \<longrightarrow> (mid = int (length a1) \<or> lo + k < mid \<and> mid < int (length a1)) \<and> sorted_sub a1 lo mid \<and> permut_sub' a a1 (nat lo) (length a1) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < lo \<longrightarrow> a1 ! nat j = a ! nat j)))) \<and> (o2 + (1 :: int) < (0 :: int) \<longrightarrow> (o1 = int (length a) \<or> lo + k < o1 \<and> o1 < int (length a)) \<and> sorted_sub a lo o1 \<and> permut_sub' a a (nat lo) (length a))))"
  sorry
end
