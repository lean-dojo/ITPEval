theory mergesort_list_OCamlMergesort_mergesortqtvc
  imports "NTP4Verif.NTP4Verif"
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
inductive sorted :: "elt list \<Rightarrow> bool" where
   Sorted_Nil: "sorted (Nil :: elt list)"
 | Sorted_One: "sorted (Cons x (Nil :: elt list))" for x :: "elt"
 | Sorted_Two: "le x y \<Longrightarrow> sorted (Cons y l) \<Longrightarrow> sorted (Cons x (Cons y l))" for x :: "elt" and y :: "elt" and l :: "elt list"
axiomatization where sorted_mem:   "(\<forall>(y :: elt). y \<in> set l \<longrightarrow> le x y) \<and> sorted l \<longleftrightarrow> sorted (Cons x l)"
  for l :: "elt list"
  and x :: "elt"
axiomatization where sorted_append:   "sorted l1 \<and> sorted l2 \<and> (\<forall>(x :: elt) (y :: elt). x \<in> set l1 \<longrightarrow> y \<in> set l2 \<longrightarrow> le x y) \<longleftrightarrow> sorted (l1 @ l2)"
  for l1 :: "elt list"
  and l2 :: "elt list"
consts prefix1 :: "int \<Rightarrow> 'a list \<Rightarrow> 'a list"
axiomatization where prefix_def1:   "prefix1 (0 :: int) l = (Nil :: 'a list)"
  for l :: "'a list"
axiomatization where prefix_def2:   "prefix1 n (Cons x l) = Cons x (prefix1 (n - (1 :: int)) l)"
 if "(0 :: int) < n"
  for n :: "int"
  and x :: "'a"
  and l :: "'a list"
theorem mergesort'vc:
  fixes l :: "elt list"
  shows "let n :: int = int (length l) in (\<not>n < (2 :: int) \<longrightarrow> (2 :: int) \<le> n \<and> n \<le> int (length l)) \<and> (\<forall>(result :: elt list). (if n < (2 :: int) then result = l else sorted result \<and> result <~~> prefix1 n l) \<longrightarrow> sorted result \<and> result <~~> l)"
  sorry
end
