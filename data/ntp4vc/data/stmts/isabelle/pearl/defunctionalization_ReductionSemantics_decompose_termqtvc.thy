theory defunctionalization_ReductionSemantics_decompose_termqtvc
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
theorem decompose_term'vc:
  fixes e :: "expr"
  fixes c :: "context"
  shows "case e of Cte n \<Rightarrow> ((0 :: int) \<le> size_e e + size_c c \<and> size_c c < size_e e + size_c c) \<and> (\<forall>(c1 :: context) (e1 :: expr). recompose c1 e1 = recompose c (Cte n) \<and> is_a_redex e1 \<longrightarrow> recompose c1 e1 = recompose c e \<and> is_a_redex e1) \<and> (is_empty_context c \<longrightarrow> is_empty_context c \<and> is_a_value e) | Sub e1 e2 \<Rightarrow> (let o1 :: context = Left c e2 in ((0 :: int) \<le> size_e e + size_c c \<and> size_e e1 + size_c o1 < size_e e + size_c c) \<and> (\<forall>(c1 :: context) (e11 :: expr). recompose c1 e11 = recompose o1 e1 \<and> is_a_redex e11 \<longrightarrow> recompose c1 e11 = recompose c e \<and> is_a_redex e11) \<and> (is_empty_context o1 \<and> is_a_value e1 \<longrightarrow> is_empty_context c \<and> is_a_value e))"
  sorry
end
