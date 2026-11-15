theory defunctionalization_ReductionSemantics_itere_optqtvc
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
theorem itere_opt'vc:
  fixes c1 :: "context"
  fixes e :: "expr"
  shows "\<forall>(c :: context) (r :: expr). recompose c r = recompose c1 e \<and> is_a_redex r \<longrightarrow> is_a_redex r \<and> (\<forall>(o1 :: expr). eval_0 o1 = eval_0 r \<longrightarrow> eval_0 (recompose c o1) = eval_0 (recompose c1 e))"
  and "is_empty_context c1 \<and> is_a_value e \<longrightarrow> (case e of Cte n \<Rightarrow> True | _ \<Rightarrow> False) \<and> (\<forall>(result :: int). (case e of Cte n \<Rightarrow> result = n | _ \<Rightarrow> False) \<longrightarrow> result = eval_0 (recompose c1 e))"
  sorry
end
