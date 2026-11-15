theory unraveling_a_card_trick_GilbreathCardTrick_card_trickqtvc
  imports "NTP4Verif.NTP4Verif" "./unraveling_a_card_trick_GilbreathCardTrickPure" "Why3STD.stack_Stack"
begin
theorem card_trick'vc:
  fixes a :: "int t"
  fixes d' :: "int t"
  assumes fact0: "stack_Stack.length a = n * m"
  assumes fact1: "suit_ordered (elts a)"
  assumes fact2: "elts d' = (Nil :: int list)"
  shows "\<exists>(result :: int). (0 :: int) \<le> result \<and> result \<le> n * m"
  and "\<forall>(cut :: int). (0 :: int) \<le> cut \<and> cut \<le> n * m \<longrightarrow> ((1 :: int) \<le> cut + (1 :: int) \<longrightarrow> (stack_Stack.length a = n * m - (1 :: int) + (1 :: int) \<and> stack_Stack.length d' = (1 :: int) - (1 :: int) \<and> elts a = rev (elts d') @ elts a) \<and> (\<forall>(d_1 :: int t) (a1 :: int t). (\<forall>(i :: int). ((1 :: int) \<le> i \<and> i \<le> cut) \<and> stack_Stack.length a1 = n * m - i + (1 :: int) \<and> stack_Stack.length d_1 = i - (1 :: int) \<and> elts a = rev (elts d_1) @ elts a1 \<longrightarrow> \<not>elts a1 = (Nil :: int list) \<and> (\<forall>(a2 :: int t) (o1 :: int). (case elts a1 of Nil \<Rightarrow> False | Cons x t \<Rightarrow> o1 = x \<and> elts a2 = t) \<longrightarrow> (\<forall>(d_2 :: int t). elts d_2 = Cons o1 (elts d_1) \<longrightarrow> stack_Stack.length a2 = n * m - (i + (1 :: int)) + (1 :: int) \<and> stack_Stack.length d_2 = i + (1 :: int) - (1 :: int) \<and> elts a = rev (elts d_2) @ elts a2))) \<and> (stack_Stack.length a1 = n * m - (cut + (1 :: int)) + (1 :: int) \<and> stack_Stack.length d_1 = cut + (1 :: int) - (1 :: int) \<and> elts a = rev (elts d_1) @ elts a1 \<longrightarrow> (\<forall>(d_2 :: int t) (a2 :: int t) (result :: int t). elts a2 = (Nil :: int list) \<and> elts d_2 = (Nil :: int list) \<and> shuffle (rev (elts a1)) (rev (elts d_1)) (elts result) \<longrightarrow> stack_Stack.length result = n * m \<and> suit_sorted (elts result))))) \<and> (cut + (1 :: int) < (1 :: int) \<longrightarrow> (\<forall>(d_1 :: int t) (a1 :: int t) (result :: int t). elts a1 = (Nil :: int list) \<and> elts d_1 = (Nil :: int list) \<and> shuffle (rev (elts a)) (rev (elts d')) (elts result) \<longrightarrow> stack_Stack.length result = n * m \<and> suit_sorted (elts result)))"
  sorry
end
