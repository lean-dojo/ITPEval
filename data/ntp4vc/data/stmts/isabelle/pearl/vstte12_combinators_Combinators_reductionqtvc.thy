theory vstte12_combinators_Combinators_reductionqtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype  "term" = S | K | App "term" "term"
fun eq :: "term \<Rightarrow> term \<Rightarrow> _"
  where "eq S S = True"
      | "eq K K = True"
      | "eq (App x1 x2) (App y1 y2) = (eq x1 y1 \<and> eq x2 y2)" for x1 x2 y1 y2
      | "eq x x0 = False" for x x0
axiomatization where eq'spec:   "eq x y \<longleftrightarrow> x = y"
  for x :: "term"
  and y :: "term"
fun is_value :: "term \<Rightarrow> _"
  where "is_value K = True"
      | "is_value S = True"
      | "is_value (App K v) = is_value v" for v
      | "is_value (App S v) = is_value v" for v
      | "is_value (App (App S v1) v2) = (is_value v1 \<and> is_value v2)" for v1 v2
      | "is_value x = False" for x
datatype  "context" = Hole | Left "context" "term" | Right "term" "context"
fun is_context :: "context \<Rightarrow> _"
  where "is_context Hole = True"
      | "is_context (Left c1 x) = is_context c1" for c1 x
      | "is_context (Right v c1) = (is_value v \<and> is_context c1)" for v c1
fun subst :: "context \<Rightarrow> term \<Rightarrow> term"
  where "subst Hole t = t" for t
      | "subst (Left c1 t2) t = App (subst c1 t) t2" for c1 t2 t
      | "subst (Right v1 c2) t = App v1 (subst c2 t)" for v1 c2 t
inductive infix_mnmngt :: "term \<Rightarrow> term \<Rightarrow> bool" where
   red_K: "is_context c \<Longrightarrow> is_value v1 \<Longrightarrow> is_value v2 \<Longrightarrow> infix_mnmngt (subst c (App (App K v1) v2)) (subst c v1)" for c :: "context" and v1 :: "term" and v2 :: "term"
 | red_S: "is_context c \<Longrightarrow> is_value v1 \<Longrightarrow> is_value v2 \<Longrightarrow> is_value v3 \<Longrightarrow> infix_mnmngt (subst c (App (App (App S v1) v2) v3)) (subst c (App (App v1 v3) (App v2 v3)))" for c :: "context" and v1 :: "term" and v2 :: "term" and v3 :: "term"
inductive relTR :: "term \<Rightarrow> term \<Rightarrow> bool" where
   BaseTransRefl: "relTR x x" for x :: "term"
 | StepTransRefl: "relTR x y \<Longrightarrow> infix_mnmngt y z \<Longrightarrow> relTR x z" for x :: "term" and y :: "term" and z :: "term"
axiomatization where relTR_transitive:   "relTR x z"
 if "relTR x y"
 and "relTR y z"
  for x :: "term"
  and y :: "term"
  and z :: "term"
datatype  zipper = ZHole | ZLeft "context" "term" | ZRight "term" "context"
fun subst_c :: "context \<Rightarrow> context \<Rightarrow> context"
  where "subst_c Hole ct = ct" for ct
      | "subst_c (Left c1 t2) ct = Left (subst_c c1 ct) t2" for c1 t2 ct
      | "subst_c (Right v1 c2) ct = Right v1 (subst_c c2 ct)" for v1 c2 ct
axiomatization where subst_c'spec:   "is_context (subst_c c ct)"
 if "is_context c"
 and "is_context ct"
  for c :: "context"
  and ct :: "context"
theorem reduction'vc:
  fixes c :: "context"
  fixes t :: "term"
  assumes fact0: "is_context c"
  shows "case t of S \<Rightarrow> (let result :: term = S in relTR (subst c t) (subst c result) \<and> is_value result) | K \<Rightarrow> (let result :: term = K in relTR (subst c t) (subst c result) \<and> is_value result) | App t1 t2 \<Rightarrow> (let o1 :: context = Left Hole t2; o2 :: context = subst_c c o1 in (is_context c \<and> is_context o1 \<longrightarrow> is_context o2) \<longrightarrow> is_context o2 \<and> (\<forall>(v1 :: term). relTR (subst o2 t1) (subst o2 v1) \<and> is_value v1 \<longrightarrow> (let o3 :: context = Right v1 Hole; o4 :: context = subst_c c o3 in (is_context c \<and> is_context o3 \<longrightarrow> is_context o4) \<longrightarrow> is_context o4 \<and> (\<forall>(v2 :: term). relTR (subst o4 t2) (subst o4 v2) \<and> is_value v2 \<longrightarrow> (case v1 of K \<Rightarrow> (let result :: term = App v1 v2 in relTR (subst c t) (subst c result) \<and> is_value result) | S \<Rightarrow> (let result :: term = App v1 v2 in relTR (subst c t) (subst c result) \<and> is_value result) | App S _ \<Rightarrow> (let result :: term = App v1 v2 in relTR (subst c t) (subst c result) \<and> is_value result) | App K v3 \<Rightarrow> relTR (subst c t) (subst c v3) \<and> is_value v3 | App (App S v3) v4 \<Rightarrow> is_context c \<and> (\<forall>(result :: term). relTR (subst c (App (App v3 v2) (App v4 v2))) (subst c result) \<and> is_value result \<longrightarrow> relTR (subst c t) (subst c result) \<and> is_value result) | _ \<Rightarrow> False)))))"
  sorry
end
