theory ropes_Balance_balanceqtvc
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
theorem balance'vc:
  fixes r :: "rope"
  assumes fact0: "inv r"
  assumes fact1: "ropes_Rope.length r < fib (max + (1 :: int))"
  shows "let o1 :: int = max + (1 :: int) in (0 :: int) \<le> o1 \<and> (\<forall>(q :: rope list). (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < o1 \<longrightarrow> q ! nat i = Emp) \<and> int (List.length q) = o1 \<longrightarrow> (((2 :: int) < int (List.length q) \<and> int (List.length q) = max + (1 :: int)) \<and> inv r \<and> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q ! nat j)) \<and> ropes_MyString.length (string_of_queue q) + ropes_Rope.length r < fib (max + (1 :: int))) \<and> (\<forall>(q1 :: rope list). List.length q1 = List.length q \<longrightarrow> (\<forall>(j :: int). (2 :: int) \<le> j \<and> j \<le> max \<longrightarrow> inv (q1 ! nat j)) \<and> infix_eqeq (string_of_queue q1) (app (string_of_queue q) (string r)) \<longrightarrow> (let o2 :: int = max in ((2 :: int) \<le> o2 + (1 :: int) \<longrightarrow> (inv Emp \<and> infix_eqeq (string Emp) (string_of_array q1 (2 :: int) (2 :: int))) \<and> (\<forall>(res :: rope). (\<forall>(i :: int). ((2 :: int) \<le> i \<and> i \<le> o2) \<and> inv res \<and> infix_eqeq (string res) (string_of_array q1 (2 :: int) i) \<longrightarrow> ((0 :: int) \<le> i \<and> i < int (List.length q1)) \<and> (let o3 :: rope = q1 ! nat i in (inv o3 \<and> inv res) \<and> (\<forall>(o4 :: rope). inv o4 \<and> infix_eqeq (string o4) (app (string o3) (string res)) \<longrightarrow> inv o4 \<and> infix_eqeq (string o4) (string_of_array q1 (2 :: int) (i + (1 :: int)))))) \<and> (inv res \<and> infix_eqeq (string res) (string_of_array q1 (2 :: int) (o2 + (1 :: int))) \<longrightarrow> inv res \<and> infix_eqeq (string res) (string r)))) \<and> (o2 + (1 :: int) < (2 :: int) \<longrightarrow> (let result :: rope = Emp in inv result \<and> infix_eqeq (string result) (string r))))))"
  sorry
end
