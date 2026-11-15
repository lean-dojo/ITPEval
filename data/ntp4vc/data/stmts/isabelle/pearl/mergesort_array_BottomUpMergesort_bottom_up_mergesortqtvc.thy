theory mergesort_array_BottomUpMergesort_bottom_up_mergesortqtvc
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
theorem bottom_up_mergesort'vc:
  fixes a :: "elt list"
  shows "let n :: int = int (length a) in \<forall>(tmp :: elt list). length tmp = length a \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length tmp) \<longrightarrow> tmp ! nat i = a ! nat i) \<longrightarrow> ((1 :: int) \<le> (1 :: int) \<and> a <~~> a \<and> (\<forall>(k :: int). let l :: int = k * (1 :: int) in (0 :: int) \<le> l \<and> l < n \<longrightarrow> sorted_sub a l (min n (l + (1 :: int))))) \<and> (\<forall>(len :: int) (tmp1 :: elt list) (a1 :: elt list). length tmp1 = length tmp \<longrightarrow> length a1 = length a \<longrightarrow> (1 :: int) \<le> len \<and> a <~~> a1 \<and> (\<forall>(k :: int). let l :: int = k * len in (0 :: int) \<le> l \<and> l < n \<longrightarrow> sorted_sub a1 l (min n (l + len))) \<longrightarrow> (if len < n then (((0 :: int) \<le> (0 :: int) \<and> (0 :: int) = (2 :: int) * (0 :: int) * len) \<and> a1 <~~> a1 \<and> (\<forall>(k :: int). let l :: int = k * len in (0 :: int) \<le> l \<and> l < n \<longrightarrow> sorted_sub a1 l (min n (l + len))) \<and> (\<forall>(k :: int). let l :: int = k * ((2 :: int) * len) in (0 :: int) \<le> l \<and> l < (0 :: int) \<longrightarrow> sorted_sub a1 l (min n (l + (2 :: int) * len)))) \<and> (\<forall>(i :: int) (tmp2 :: elt list) (a2 :: elt list). length tmp2 = length tmp1 \<longrightarrow> length a2 = length a1 \<longrightarrow> (0 :: int) \<le> (2 :: int) * i * len \<and> a1 <~~> a2 \<and> (\<forall>(k :: int). let l :: int = k * len in (2 :: int) * i * len \<le> l \<and> l < n \<longrightarrow> sorted_sub a2 l (min n (l + len))) \<and> (\<forall>(k :: int). let l :: int = k * ((2 :: int) * len) in (0 :: int) \<le> l \<and> l < (2 :: int) * i * len \<longrightarrow> sorted_sub a2 l (min n (l + (2 :: int) * len))) \<longrightarrow> (if (2 :: int) * i * len < n - len then let mid :: int = (2 :: int) * i * len + len; hi :: int = min n (mid + len) in (((0 :: int) \<le> (2 :: int) * i * len \<and> (2 :: int) * i * len \<le> mid \<and> mid \<le> hi \<and> hi \<le> int (length tmp2) \<and> length tmp2 = length a2) \<and> sorted_sub a2 ((2 :: int) * i * len) mid \<and> sorted_sub a2 mid hi) \<and> (\<forall>(a3 :: elt list). length a3 = length a2 \<longrightarrow> sorted_sub a3 ((2 :: int) * i * len) hi \<and> permut_sub a2 a3 (nat ((2 :: int) * i * len)) (nat hi) \<and> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < (2 :: int) * i * len \<or> hi \<le> i1 \<and> i1 < int (length a3) \<longrightarrow> a3 ! nat i1 = a2 ! nat i1) \<longrightarrow> ((0 :: int) \<le> n + len - (2 :: int) * i * len \<and> n + len - (mid + len) < n + len - (2 :: int) * i * len) \<and> ((0 :: int) \<le> mid + len \<and> mid + len = (2 :: int) * (i + (1 :: int)) * len) \<and> a1 <~~> a3 \<and> (\<forall>(k :: int). let l :: int = k * len in mid + len \<le> l \<and> l < n \<longrightarrow> sorted_sub a3 l (min n (l + len))) \<and> (\<forall>(k :: int). let l :: int = k * ((2 :: int) * len) in (0 :: int) \<le> l \<and> l < mid + len \<longrightarrow> sorted_sub a3 l (min n (l + (2 :: int) * len)))) else ((0 :: int) \<le> (2 :: int) * n - len \<and> (2 :: int) * n - (2 :: int) * len < (2 :: int) * n - len) \<and> (1 :: int) \<le> (2 :: int) * len \<and> a <~~> a2 \<and> (\<forall>(k :: int). let l :: int = k * ((2 :: int) * len) in (0 :: int) \<le> l \<and> l < n \<longrightarrow> sorted_sub a2 l (min n (l + (2 :: int) * len))))) else sorted a1 \<and> a <~~> a1))"
  sorry
end
