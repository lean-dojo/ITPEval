theory cursor_examples_TestListCursor_list_sumqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Sum" "./cursor_examples_ListCursorImpl"
begin
consts get_closure :: "'a list \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where get_closure_def:   "get_closure y y1 = y ! nat y1"
  for y :: "'a list"
  and y1 :: "int"
theorem list_sum'vc:
  fixes c :: "int cursor"
  fixes l :: "int list"
  assumes fact0: "permitted c"
  assumes fact1: "visited c = []"
  assumes fact2: "collection c = l"
  shows "(0 :: int) = sum (get_closure (visited c)) (0 :: int) (int (length (visited c)))"
  and "permitted c"
  and "\<forall>(c1 :: int cursor). collection c1 = collection c \<longrightarrow> permitted c1 \<longrightarrow> permitted c1 \<and> (if \<not>complete c1 then (\<not>complete c1 \<and> permitted c1) \<and> (\<forall>(c2 :: int cursor). collection c2 = collection c1 \<longrightarrow> (\<forall>(x :: int). visited c2 = visited c1 @ [x] \<and> permitted c2 \<longrightarrow> ((0 :: int) \<le> int (length l) - int (length (visited c1)) \<and> int (length l) - int (length (visited c2)) < int (length l) - int (length (visited c1))) \<and> sum (get_closure (visited c1)) (0 :: int) (int (length (visited c1))) + x = sum (get_closure (visited c2)) (0 :: int) (int (length (visited c2))) \<and> permitted c2)) else sum (get_closure (visited c1)) (0 :: int) (int (length (visited c1))) = sum_list l)"
  sorry
end
