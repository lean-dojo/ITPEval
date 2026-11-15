theory defunctionalization_RWithError_interpretqtvc
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
theorem interpret'vc:
  fixes p :: "expr"
  shows "defunctionalization_SemWithError.eval_0 (recompose (Empty :: context) p) = defunctionalization_SemWithError.eval_0 p"
  sorry
end
