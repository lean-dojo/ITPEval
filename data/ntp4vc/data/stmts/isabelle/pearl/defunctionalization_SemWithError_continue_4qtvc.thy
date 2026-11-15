theory defunctionalization_SemWithError_continue_4qtvc
  imports "NTP4Verif.NTP4Verif" "./defunctionalization_Expr" "./defunctionalization_DirectSem" "./defunctionalization_Defunctionalization"
begin
datatype  "value" = Vnum "int" | Underflow
fun eval_0 :: "expr \<Rightarrow> value"
  where "eval_0 (Cte n) = (if (0 :: int) \<le> n then Vnum n else Underflow)" for n
      | "eval_0 (Sub e1 e2) = (case eval_0 e1 of Underflow \<Rightarrow> Underflow | Vnum v1 \<Rightarrow> (case eval_0 e2 of Underflow \<Rightarrow> Underflow | Vnum v2 \<Rightarrow> (if v2 \<le> v1 then Vnum (v1 - v2) else Underflow)))" for e1 e2
consts fc :: "(value \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> value \<Rightarrow> 'a"
consts fc1 :: "(value \<Rightarrow> 'a) \<Rightarrow> expr \<Rightarrow> value \<Rightarrow> 'a"
axiomatization where fc'def:   "fc k v1 v2 = (case v2 of Underflow \<Rightarrow> k Underflow | Vnum v21 \<Rightarrow> k (if v21 \<le> v1 then Vnum (v1 - v21) else Underflow))"
  for k :: "value \<Rightarrow> 'a"
  and v1 :: "int"
  and v2 :: "value"
fun eval_1 :: "expr \<Rightarrow> (value \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "eval_1 (Cte n) k = k (if (0 :: int) \<le> n then Vnum n else Underflow)" for n k
      | "eval_1 (Sub e1 e2) k = eval_1 e1 (fc1 k e2)" for e1 e2 k
axiomatization where fc'def1:   "fc1 k e2 v1 = (case v1 of Underflow \<Rightarrow> k Underflow | Vnum v11 \<Rightarrow> eval_1 e2 (fc k v11))"
  for k :: "value \<Rightarrow> 'a"
  and e2 :: "expr"
  and v1 :: "value"
consts identity :: "value \<Rightarrow> value"
axiomatization where identity_def:   "identity y = y"
  for y :: "value"
definition interpret_1 :: "expr \<Rightarrow> value"
  where "interpret_1 p = eval_1 p identity" for p
consts eval_2a :: "expr \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a"
consts eval_2b :: "int \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where eval_2b'def:   "eval_2b v1 k kerr v2 = (if v2 \<le> v1 then k (v1 - v2) else kerr ())"
  for v1 :: "int"
  and k :: "int \<Rightarrow> 'a"
  and kerr :: "unit \<Rightarrow> 'a"
  and v2 :: "int"
fun eval_2 :: "expr \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "eval_2 (Cte n) k kerr = (if (0 :: int) \<le> n then k n else kerr ())" for n k kerr
      | "eval_2 (Sub e1 e2) k kerr = eval_2 e1 (eval_2a e2 k kerr) kerr" for e1 e2 k kerr
axiomatization where eval_2a'def:   "eval_2a e2 k kerr v1 = eval_2 e2 (eval_2b v1 k kerr) kerr"
  for e2 :: "expr"
  and k :: "int \<Rightarrow> 'a"
  and kerr :: "unit \<Rightarrow> 'a"
  and v1 :: "int"
consts Vnum_closure :: "int \<Rightarrow> value"
consts fc2 :: "unit \<Rightarrow> value"
axiomatization where Vnum_closure_def:   "Vnum_closure y = Vnum y"
  for y :: "int"
axiomatization where fc'def2:   "fc2 x = Underflow"
  for x :: "unit"
definition interpret_2 :: "expr \<Rightarrow> value"
  where "interpret_2 p = eval_2 p Vnum_closure fc2" for p
consts eval_3a :: "expr \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> int \<Rightarrow> value"
consts eval_3b :: "int \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> int \<Rightarrow> value"
axiomatization where eval_3b'def:   "eval_3b v1 k v2 = (if v2 \<le> v1 then k (v1 - v2) else Underflow)"
  for v1 :: "int"
  and k :: "int \<Rightarrow> value"
  and v2 :: "int"
fun eval_3 :: "expr \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> value"
  where "eval_3 (Cte n) k = (if (0 :: int) \<le> n then k n else Underflow)" for n k
      | "eval_3 (Sub e1 e2) k = eval_3 e1 (eval_3a e2 k)" for e1 e2 k
axiomatization where eval_3a'def:   "eval_3a e2 k v1 = eval_3 e2 (eval_3b v1 k)"
  for e2 :: "expr"
  and k :: "int \<Rightarrow> value"
  and v1 :: "int"
definition interpret_3 :: "expr \<Rightarrow> value"
  where "interpret_3 p = eval_3 p Vnum_closure" for p
datatype  cont = I | A "expr" "cont" | B "int" "cont"
inductive eval_cont :: "cont \<Rightarrow> value \<Rightarrow> value \<Rightarrow> bool" where
   underflow: "eval_cont k Underflow Underflow" for k :: "cont"
 | a1: "eval_cont (B v k) (eval_0 e2) r \<Longrightarrow> eval_cont (A e2 k) (Vnum v) r" for v :: "int" and k :: "cont" and e2 :: "expr" and r :: "value"
 | a2: "eval_cont k (if v \<le> v1 then Vnum (v1 - v) else Underflow) r \<Longrightarrow> eval_cont (B v1 k) (Vnum v) r" for k :: "cont" and v :: "int" and v1 :: "int" and r :: "value"
 | a3: "eval_cont I (Vnum v) (Vnum v)" for v :: "int"
fun size_e :: "expr \<Rightarrow> int"
  where "size_e (Cte x) = (1 :: int)" for x
      | "size_e (Sub e1 e2) = (3 :: int) + size_e e1 + size_e e2" for e1 e2
fun size_c :: "cont \<Rightarrow> int"
  where "size_c I = (0 :: int)"
      | "size_c (A e2 k) = (2 :: int) + defunctionalization_Defunctionalization.size_e e2 + size_c k" for e2 k
      | "size_c (B x k) = (1 :: int) + size_c k" for x k
theorem continue_4'vc:
  fixes v :: "int"
  fixes c :: "cont"
  assumes fact0: "(0 :: int) \<le> v"
  shows "case c of A e2 k \<Rightarrow> (0 :: int) \<le> size_c c \<and> size_c (B v k) + defunctionalization_Defunctionalization.size_e e2 < size_c c | B v1 k \<Rightarrow> v \<le> v1 \<longrightarrow> ((0 :: int) \<le> size_c c \<and> size_c k < size_c c) \<and> (0 :: int) \<le> v1 - v | I \<Rightarrow> True"
  and "\<forall>(result :: value). (case c of A e2 k \<Rightarrow> eval_cont (B v k) (eval_0 e2) result | B v1 k \<Rightarrow> (if v \<le> v1 then eval_cont k (Vnum (v1 - v)) result else result = Underflow) | I \<Rightarrow> result = Vnum v) \<longrightarrow> eval_cont c (Vnum v) result"
  sorry
end
