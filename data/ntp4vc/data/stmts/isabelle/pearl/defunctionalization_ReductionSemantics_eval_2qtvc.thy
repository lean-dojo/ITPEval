theory defunctionalization_ReductionSemantics_eval_2qtvc
  imports "NTP4Verif.NTP4Verif" "./defunctionalization_Expr" "./defunctionalization_DirectSem" "./defunctionalization_Defunctionalization"
begin
definition is_a_redex :: "expr \<Rightarrow> _"
  where "is_a_redex e \<longleftrightarrow> (case e of Sub (Cte _) (Cte _) \<Rightarrow> True | _ \<Rightarrow> False)" for e
datatype  "context" = Empty | Left "context" "expr" | Right "int" "context"
fun recompose :: "context \<Rightarrow> expr \<Rightarrow> expr"
  where "recompose (Empty :: context) e = e" for e
      | "recompose (Left c1 e2) e = recompose c1 (Sub e e2)" for c1 e2 e
      | "recompose (Right n1 c1) e = recompose c1 (Sub (Cte n1) e)" for n1 c1 e
definition is_a_value :: "expr \<Rightarrow> _"
  where "is_a_value e \<longleftrightarrow> (case e of Cte _ \<Rightarrow> True | _ \<Rightarrow> False)" for e
definition is_empty_context :: "context \<Rightarrow> _"
  where "is_empty_context c \<longleftrightarrow> (case c of (Empty :: context) \<Rightarrow> True | _ \<Rightarrow> False)" for c
fun size_c :: "context \<Rightarrow> int"
  where "size_c (Empty :: context) = (0 :: int)"
      | "size_c (Left c1 e) = (2 :: int) + size_c c1 + size_e e" for c1 e
      | "size_c (Right x c1) = (1 :: int) + size_c c1" for x c1
theorem eval_2'vc:
  fixes c :: "context"
  fixes n :: "int"
  shows "case c of (Empty :: context) \<Rightarrow> True | Left c1 e \<Rightarrow> (0 :: int) \<le> (1 :: int) + (2 :: int) * size_c c \<and> (2 :: int) * (size_c (Right n c1) + size_e e) < (1 :: int) + (2 :: int) * size_c c | Right n1 c1 \<Rightarrow> (0 :: int) \<le> (1 :: int) + (2 :: int) * size_c c \<and> (2 :: int) * (size_c c1 + size_e (Cte (n1 - n))) < (1 :: int) + (2 :: int) * size_c c"
  and "\<forall>(result :: int). (case c of (Empty :: context) \<Rightarrow> result = n | Left c1 e \<Rightarrow> result = eval_0 (recompose (Right n c1) e) | Right n1 c1 \<Rightarrow> result = eval_0 (recompose c1 (Cte (n1 - n)))) \<longrightarrow> result = eval_0 (recompose c (Cte n))"
  sorry
end
