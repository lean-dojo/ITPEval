theory ropes_Balance_insert_leavesqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Fibonacci" "./ropes_MyString" "./ropes_Rope"
begin
consts max :: "int"
axiomatization where max'def:   "(2 :: int) \<le> max"
consts string_of_array :: "rope list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> char_string"
axiomatization where string_of_array_empty:   "infix_eqeq (string_of_array q l l) ropes_MyString.empty"
 if "(0 :: int) \<le> l"
 and "l \<le> int (List.length q)"
  for l :: "int"
  and q :: "rope list"
axiomatization where string_of_array_concat_left:   "infix_eqeq (string_of_array q l u) (app (string_of_array q (l + (1 :: int)) u) (string (q ! nat l)))"
 if "(0 :: int) \<le> l"
 and "l < u"
 and "u \<le> int (List.length q)"
  for l :: "int"
  and u :: "int"
  and q :: "rope list"
definition string_of_queue :: "rope list \<Rightarrow> char_string"
  where "string_of_queue q = string_of_array q (2 :: int) (int (List.length q))" for q
theorem insert_leaves'vc:
  fixes q :: "rope list"
  fixes r :: "rope"
  assumes fact0: "(2 :: int) < int (List.length q)"
  assumes fact1: "int (List.length q) = max + (1 :: int)"
  assumes fact2: "inv r"
  assumes fact3: "\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q ! nat j)"
  assumes fact4: "ropes_MyString.length (string_of_queue q) + ropes_Rope.length r < fib (max + (1 :: int))"
  shows "case r of Emp \<Rightarrow> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q ! nat j)) \<and> infix_eqeq (string_of_queue q) (app (string_of_queue q) (string r)) | Str _ _ _ \<Rightarrow> (((2 :: int) \<le> (2 :: int) \<and> (2 :: int) < int (List.length q) \<and> int (List.length q) = max + (1 :: int)) \<and> inv r \<and> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q ! nat j)) \<and> ropes_MyString.length (string_of_array q (2 :: int) (max + (1 :: int))) + ropes_Rope.length r < fib (max + (1 :: int))) \<and> (\<forall>(q1 :: rope list). List.length q1 = List.length q \<longrightarrow> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q1 ! nat j)) \<and> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j < (2 :: int) \<longrightarrow> q1 ! nat j = q ! nat j) \<and> infix_eqeq (string_of_array q1 (2 :: int) (max + (1 :: int))) (app (string_of_array q (2 :: int) (max + (1 :: int))) (string r)) \<longrightarrow> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q1 ! nat j)) \<and> infix_eqeq (string_of_queue q1) (app (string_of_queue q) (string r))) | App left1 right1 _ \<Rightarrow> ((case r of Emp \<Rightarrow> False | Str _ _ _ \<Rightarrow> False | App f f1 _ \<Rightarrow> f = left1 \<or> f1 = left1) \<and> ((2 :: int) < int (List.length q) \<and> int (List.length q) = max + (1 :: int)) \<and> inv left1 \<and> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q ! nat j)) \<and> ropes_MyString.length (string_of_queue q) + ropes_Rope.length left1 < fib (max + (1 :: int))) \<and> (\<forall>(q1 :: rope list). List.length q1 = List.length q \<longrightarrow> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q1 ! nat j)) \<and> infix_eqeq (string_of_queue q1) (app (string_of_queue q) (string left1)) \<longrightarrow> ((case r of Emp \<Rightarrow> False | Str _ _ _ \<Rightarrow> False | App f f1 _ \<Rightarrow> f = right1 \<or> f1 = right1) \<and> ((2 :: int) < int (List.length q1) \<and> int (List.length q1) = max + (1 :: int)) \<and> inv right1 \<and> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q1 ! nat j)) \<and> ropes_MyString.length (string_of_queue q1) + ropes_Rope.length right1 < fib (max + (1 :: int))) \<and> (\<forall>(q2 :: rope list). List.length q2 = List.length q1 \<longrightarrow> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q2 ! nat j)) \<and> infix_eqeq (string_of_queue q2) (app (string_of_queue q1) (string right1)) \<longrightarrow> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q2 ! nat j)) \<and> infix_eqeq (string_of_queue q2) (app (string_of_queue q) (string r))))"
  sorry
end
