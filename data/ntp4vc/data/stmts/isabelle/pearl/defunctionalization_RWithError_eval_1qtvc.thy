theory defunctionalization_RWithError_eval_1qtvc
  imports "NTP4Verif.NTP4Verif" "./defunctionalization_Expr" "./defunctionalization_DirectSem" "./defunctionalization_Defunctionalization" "./defunctionalization_SemWithError"
begin
datatype  "context" = Empty | Left "context" "expr" | Right "int" "context"
fun size_c :: "context \<Rightarrow> int"
  where "size_c (Empty :: context) = (0 :: int)"
      | "size_c (Left c1 e) = (2 :: int) + size_c c1 + defunctionalization_Defunctionalization.size_e e" for c1 e
      | "size_c (Right x c1) = (1 :: int) + size_c c1" for x c1
fun recompose :: "context \<Rightarrow> expr \<Rightarrow> expr"
  where "recompose (Empty :: context) e = e" for e
      | "recompose (Left c1 e2) e = recompose c1 (Sub e e2)" for c1 e2 e
      | "recompose (Right n1 c1) e = recompose c1 (Sub (Cte n1) e)" for n1 c1 e
theorem eval_1'vc:
  fixes e :: "expr"
  fixes c :: "context"
  shows "case e of Cte n \<Rightarrow> (0 :: int) \<le> n \<longrightarrow> ((0 :: int) \<le> (2 :: int) * (size_c c + defunctionalization_Defunctionalization.size_e e) \<and> (1 :: int) + (2 :: int) * size_c c < (2 :: int) * (size_c c + defunctionalization_Defunctionalization.size_e e)) \<and> (0 :: int) \<le> n | Sub e1 e2 \<Rightarrow> (0 :: int) \<le> (2 :: int) * (size_c c + defunctionalization_Defunctionalization.size_e e) \<and> (2 :: int) * (size_c (Left c e2) + defunctionalization_Defunctionalization.size_e e1) < (2 :: int) * (size_c c + defunctionalization_Defunctionalization.size_e e)"
  and "\<forall>(result :: value). (case e of Cte n \<Rightarrow> (if (0 :: int) \<le> n then result = defunctionalization_SemWithError.eval_0 (recompose c (Cte n)) else result = Underflow) | Sub e1 e2 \<Rightarrow> result = defunctionalization_SemWithError.eval_0 (recompose (Left c e2) e1)) \<longrightarrow> result = defunctionalization_SemWithError.eval_0 (recompose c e)"
  sorry
end
