theory mergesort_array_NaturalMergesort_natural_mergesortqtvc
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
theorem natural_mergesort'vc:
  fixes a :: "elt list"
  shows "let n :: int = int (length a) in if n \<le> (1 :: int) then sorted a \<and> a <~~> a else \<forall>(tmp :: elt list). length tmp = length a \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length tmp) \<longrightarrow> tmp ! nat i = a ! nat i) \<longrightarrow> ((((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> n) \<and> sorted_sub a (0 :: int) (0 :: int)) \<and> a <~~> a) \<and> (\<forall>(first_run :: int) (tmp1 :: elt list) (a1 :: elt list). length tmp1 = length tmp \<longrightarrow> length a1 = length a \<longrightarrow> (((0 :: int) \<le> first_run \<and> first_run \<le> n) \<and> sorted_sub a1 (0 :: int) first_run) \<and> a <~~> a1 \<longrightarrow> (((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> n) \<and> (first_run \<le> first_run \<and> first_run \<le> n) \<and> sorted_sub a1 (0 :: int) first_run \<and> a1 <~~> a1) \<and> (\<forall>(lo :: int) (first_run1 :: int) (tmp2 :: elt list) (a2 :: elt list). length tmp2 = length tmp1 \<longrightarrow> length a2 = length a1 \<longrightarrow> ((0 :: int) \<le> lo \<and> lo \<le> n) \<and> (first_run \<le> first_run1 \<and> first_run1 \<le> n) \<and> sorted_sub a2 (0 :: int) first_run1 \<and> (lo = (0 :: int) \<or> first_run1 \<le> lo \<and> first_run < first_run1) \<and> a1 <~~> a2 \<longrightarrow> (if lo < n - (1 :: int) then ((0 :: int) \<le> lo \<and> lo < int (length a2)) \<and> (\<forall>(mid :: int). (lo < mid \<and> mid \<le> int (length a2)) \<and> sorted_sub a2 lo mid \<and> (mid < int (length a2) \<longrightarrow> \<not>le (a2 ! nat (mid - (1 :: int))) (a2 ! nat mid)) \<longrightarrow> (if mid = n then if lo = (0 :: int) then sorted a2 \<and> a <~~> a2 else ((0 :: int) \<le> n - first_run \<and> n - first_run1 < n - first_run) \<and> (((0 :: int) \<le> first_run1 \<and> first_run1 \<le> n) \<and> sorted_sub a2 (0 :: int) first_run1) \<and> a <~~> a2 else ((0 :: int) \<le> mid \<and> mid < int (length a2)) \<and> (\<forall>(hi :: int). (mid < hi \<and> hi \<le> int (length a2)) \<and> sorted_sub a2 mid hi \<and> (hi < int (length a2) \<longrightarrow> \<not>le (a2 ! nat (hi - (1 :: int))) (a2 ! nat hi)) \<longrightarrow> (((0 :: int) \<le> lo \<and> lo \<le> mid \<and> mid \<le> hi \<and> hi \<le> int (length tmp2) \<and> length tmp2 = length a2) \<and> sorted_sub a2 lo mid \<and> sorted_sub a2 mid hi) \<and> (\<forall>(a3 :: elt list). length a3 = length a2 \<longrightarrow> sorted_sub a3 lo hi \<and> permut_sub a2 a3 (nat lo) (nat hi) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < lo \<or> hi \<le> i \<and> i < int (length a3) \<longrightarrow> a3 ! nat i = a2 ! nat i) \<longrightarrow> (if lo = (0 :: int) then ((0 :: int) \<le> n - lo \<and> n - hi < n - lo) \<and> ((0 :: int) \<le> hi \<and> hi \<le> n) \<and> (first_run \<le> hi \<and> hi \<le> n) \<and> sorted_sub a3 (0 :: int) hi \<and> (hi = (0 :: int) \<or> hi \<le> hi \<and> first_run < hi) \<and> a1 <~~> a3 else ((0 :: int) \<le> n - lo \<and> n - hi < n - lo) \<and> ((0 :: int) \<le> hi \<and> hi \<le> n) \<and> (first_run \<le> first_run1 \<and> first_run1 \<le> n) \<and> sorted_sub a3 (0 :: int) first_run1 \<and> (hi = (0 :: int) \<or> first_run1 \<le> hi \<and> first_run < first_run1) \<and> a1 <~~> a3))))) else ((0 :: int) \<le> n - first_run \<and> n - first_run1 < n - first_run) \<and> (((0 :: int) \<le> first_run1 \<and> first_run1 \<le> n) \<and> sorted_sub a2 (0 :: int) first_run1) \<and> a <~~> a2)))"
  sorry
end
