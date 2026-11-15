theory defunctionalization_RWithError_eval_2qtvc
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
theorem eval_2'vc:
  fixes n :: "int"
  fixes c :: "context"
  assumes fact0: "(0 :: int) \<le> n"
  shows "case c of (Empty :: context) \<Rightarrow> True | Left c1 e \<Rightarrow> (0 :: int) \<le> (1 :: int) + (2 :: int) * size_c c \<and> (2 :: int) * (size_c (Right n c1) + defunctionalization_Defunctionalization.size_e e) < (1 :: int) + (2 :: int) * size_c c | Right n1 c1 \<Rightarrow> n \<le> n1 \<longrightarrow> (0 :: int) \<le> (1 :: int) + (2 :: int) * size_c c \<and> (2 :: int) * (size_c c1 + defunctionalization_Defunctionalization.size_e (Cte (n1 - n))) < (1 :: int) + (2 :: int) * size_c c"
  and "\<forall>(result :: value). (case c of (Empty :: context) \<Rightarrow> result = Vnum n | Left c1 e \<Rightarrow> result = defunctionalization_SemWithError.eval_0 (recompose (Right n c1) e) | Right n1 c1 \<Rightarrow> (if n \<le> n1 then result = defunctionalization_SemWithError.eval_0 (recompose c1 (Cte (n1 - n))) else result = Underflow)) \<longrightarrow> result = defunctionalization_SemWithError.eval_0 (recompose c (Cte n))"
  sorry
end
