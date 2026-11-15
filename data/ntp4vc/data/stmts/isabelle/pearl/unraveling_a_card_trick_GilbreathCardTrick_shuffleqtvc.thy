theory unraveling_a_card_trick_GilbreathCardTrick_shuffleqtvc
  imports "NTP4Verif.NTP4Verif" "./unraveling_a_card_trick_GilbreathCardTrickPure" "Why3STD.stack_Stack"
begin
theorem shuffle'vc:
  fixes c :: "int t"
  fixes a' :: "int t"
  fixes b' :: "int t"
  fixes a :: "int t"
  fixes b :: "int t"
  assumes fact0: "elts c = (Nil :: int list)"
  assumes fact1: "elts a' = (Nil :: int list)"
  assumes fact2: "elts b' = (Nil :: int list)"
  shows "rev (elts a) = rev (elts a) @ elts a'"
  and "rev (elts b) = rev (elts b) @ elts b'"
  and "shuffle (elts a') (elts b') (elts c)"
  and "\<forall>(b'1 :: int t) (a'1 :: int t) (c1 :: int t) (b1 :: int t) (a1 :: int t). rev (elts a) = rev (elts a1) @ elts a'1 \<and> rev (elts b) = rev (elts b1) @ elts b'1 \<and> shuffle (elts a'1) (elts b'1) (elts c1) \<longrightarrow> (\<forall>(o1 :: bool). (if elts a1 = (Nil :: int list) then o1 = (if elts b1 = (Nil :: int list) then True else False) else o1 = False) \<longrightarrow> (if \<not>o1 = True then \<forall>(o2 :: bool). (if \<not>elts a1 = (Nil :: int list) then elts b1 = (Nil :: int list) \<longrightarrow> o2 = True else o2 = False) \<longrightarrow> (if o2 = True then \<not>elts a1 = (Nil :: int list) \<and> (\<forall>(o3 :: int). (case elts a1 of Nil \<Rightarrow> False | Cons x _ \<Rightarrow> o3 = x) \<longrightarrow> (\<forall>(a'2 :: int t). elts a'2 = Cons o3 (elts a'1) \<longrightarrow> \<not>elts a1 = (Nil :: int list) \<and> (\<forall>(a2 :: int t) (o4 :: int). (case elts a1 of Nil \<Rightarrow> False | Cons x t \<Rightarrow> o4 = x \<and> elts a2 = t) \<longrightarrow> (\<forall>(c2 :: int t). elts c2 = Cons o4 (elts c1) \<longrightarrow> ((0 :: int) \<le> stack_Stack.length a1 + stack_Stack.length b1 \<and> stack_Stack.length a2 + stack_Stack.length b1 < stack_Stack.length a1 + stack_Stack.length b1) \<and> rev (elts a) = rev (elts a2) @ elts a'2 \<and> rev (elts b) = rev (elts b1) @ elts b'1 \<and> shuffle (elts a'2) (elts b'1) (elts c2))))) else \<not>elts b1 = (Nil :: int list) \<and> (\<forall>(o3 :: int). (case elts b1 of Nil \<Rightarrow> False | Cons x _ \<Rightarrow> o3 = x) \<longrightarrow> (\<forall>(b'2 :: int t). elts b'2 = Cons o3 (elts b'1) \<longrightarrow> \<not>elts b1 = (Nil :: int list) \<and> (\<forall>(b2 :: int t) (o4 :: int). (case elts b1 of Nil \<Rightarrow> False | Cons x t \<Rightarrow> o4 = x \<and> elts b2 = t) \<longrightarrow> (\<forall>(c2 :: int t). elts c2 = Cons o4 (elts c1) \<longrightarrow> ((0 :: int) \<le> stack_Stack.length a1 + stack_Stack.length b1 \<and> stack_Stack.length a1 + stack_Stack.length b2 < stack_Stack.length a1 + stack_Stack.length b1) \<and> rev (elts a) = rev (elts a1) @ elts a'1 \<and> rev (elts b) = rev (elts b2) @ elts b'2 \<and> shuffle (elts a'1) (elts b'2) (elts c2)))))) else elts a1 = (Nil :: int list) \<and> elts b1 = (Nil :: int list) \<and> shuffle (rev (elts a)) (rev (elts b)) (elts c1)))"
  sorry
end
