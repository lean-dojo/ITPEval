theory defunctionalization_Defunctionalization_continue_2qtvc
  imports "NTP4Verif.NTP4Verif" "./defunctionalization_Expr" "./defunctionalization_DirectSem"
begin
datatype  cont = A1 "expr" "cont" | A2 "int" "cont" | I
inductive eval_cont :: "cont \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
   a1: "eval_cont (A2 v k) (eval_0 e2) r \<Longrightarrow> eval_cont (A1 e2 k) v r" for v :: "int" and k :: "cont" and e2 :: "expr" and r :: "int"
 | a2: "eval_cont k (v1 - v) r \<Longrightarrow> eval_cont (A2 v1 k) v r" for k :: "cont" and v1 :: "int" and v :: "int" and r :: "int"
 | a3: "eval_cont I v v" for v :: "int"
fun size_e :: "expr \<Rightarrow> int"
  where "size_e (Cte x) = (1 :: int)" for x
      | "size_e (Sub e1 e2) = (3 :: int) + size_e e1 + size_e e2" for e1 e2
fun size_c :: "cont \<Rightarrow> int"
  where "size_c I = (0 :: int)"
      | "size_c (A1 e2 k) = (2 :: int) + size_e e2 + size_c k" for e2 k
      | "size_c (A2 x k) = (1 :: int) + size_c k" for x k
theorem continue_2'vc:
  fixes c :: "cont"
  fixes v :: "int"
  shows "case c of A1 e2 k \<Rightarrow> (0 :: int) \<le> size_c c \<and> size_c (A2 v k) + size_e e2 < size_c c | A2 v1 k \<Rightarrow> (0 :: int) \<le> size_c c \<and> size_c k < size_c c | I \<Rightarrow> True"
  and "\<forall>(result :: int). (case c of A1 e2 k \<Rightarrow> eval_cont (A2 v k) (eval_0 e2) result | A2 v1 k \<Rightarrow> eval_cont k (v1 - v) result | I \<Rightarrow> result = v) \<longrightarrow> eval_cont c v result"
  sorry
end
