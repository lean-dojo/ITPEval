theory sorted_list_FindInSortedList_findqtvc
  imports "NTP4Verif.NTP4Verif"
begin
theorem find'vc:
  fixes l :: "int list"
  fixes x :: "int"
  assumes fact0: "sorted l"
  shows "case l of Nil \<Rightarrow> True | Cons y r \<Rightarrow> \<not>x = y \<longrightarrow> y < x \<longrightarrow> (case l of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = r) \<and> sorted r"
  and "\<forall>(result :: bool). (case l of Nil \<Rightarrow> result = False | Cons y r \<Rightarrow> (if x = y then result = True else if y < x then result = (if x \<in> set r then True else False) else result = False)) \<longrightarrow> result = True \<longleftrightarrow> x \<in> set l"
  sorry
end
