theory vstte12_combinators_Combinators_reduction3qtvc
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
definition irreducible :: "term \<Rightarrow> _"
  where "irreducible t \<longleftrightarrow> (\<forall>(t' :: term). \<not>infix_mnmngt t t')" for t
inductive only_K :: "term \<Rightarrow> bool" where
   only_K_K: "only_K K"
 | only_K_App: "only_K t1 \<Longrightarrow> only_K t2 \<Longrightarrow> only_K (App t1 t2)" for t1 :: "term" and t2 :: "term"
consts ks :: "int \<Rightarrow> term"
axiomatization where ks'def:   "if n = (0 :: int) then ks n = K else ks n = App (ks (n - (1 :: int))) K"
 if "(0 :: int) \<le> n"
  for n :: "int"
axiomatization where ks'spec:   "only_K (ks n)"
 if "(0 :: int) \<le> n"
  for n :: "int"
theorem reduction3'vc:
  fixes n :: "int"
  fixes c :: "context"
  assumes fact0: "(0 :: int) \<le> n"
  assumes fact1: "is_context c"
  shows "case ks n of K \<Rightarrow> True | App t1 t2 \<Rightarrow> (let o1 :: int = n - (1 :: int); o2 :: context = Left Hole t2; o3 :: context = subst_c c o2 in (is_context c \<and> is_context o2 \<longrightarrow> is_context o3) \<longrightarrow> (((0 :: int) \<le> n \<and> o1 < n) \<and> (0 :: int) \<le> o1 \<and> t1 = ks o1 \<and> is_context o3) \<and> (\<forall>(v1 :: term). relTR (subst o3 t1) (subst o3 v1) \<and> is_value v1 \<and> (even o1 \<longrightarrow> v1 = K) \<and> (odd o1 \<longrightarrow> v1 = App K K) \<longrightarrow> (let o4 :: context = Right v1 Hole; o5 :: context = subst_c c o4 in (is_context c \<and> is_context o4 \<longrightarrow> is_context o5) \<longrightarrow> (((0 :: int) \<le> n \<and> (0 :: int) < n) \<and> (0 :: int) \<le> (0 :: int) \<and> t2 = ks (0 :: int) \<and> is_context o5) \<and> (\<forall>(v2 :: term). relTR (subst o5 t2) (subst o5 v2) \<and> is_value v2 \<and> (even (0 :: int) \<longrightarrow> v2 = K) \<and> (odd (0 :: int) \<longrightarrow> v2 = App K K) \<longrightarrow> (case v1 of K \<Rightarrow> True | App K v3 \<Rightarrow> True | _ \<Rightarrow> False))))) | _ \<Rightarrow> False"
  and "\<forall>(result :: term). (case ks n of K \<Rightarrow> result = K | App t1 t2 \<Rightarrow> (let o1 :: int = n - (1 :: int); o2 :: context = Left Hole t2; o3 :: context = subst_c c o2 in (is_context c \<and> is_context o2 \<longrightarrow> is_context o3) \<and> (\<exists>(v1 :: term). (relTR (subst o3 t1) (subst o3 v1) \<and> is_value v1 \<and> (even o1 \<longrightarrow> v1 = K) \<and> (odd o1 \<longrightarrow> v1 = App K K)) \<and> (let o4 :: context = Right v1 Hole; o5 :: context = subst_c c o4 in (is_context c \<and> is_context o4 \<longrightarrow> is_context o5) \<and> (\<exists>(v2 :: term). (relTR (subst o5 t2) (subst o5 v2) \<and> is_value v2 \<and> (even (0 :: int) \<longrightarrow> v2 = K) \<and> (odd (0 :: int) \<longrightarrow> v2 = App K K)) \<and> (case v1 of K \<Rightarrow> result = App v1 v2 | App K v3 \<Rightarrow> result = v3 | _ \<Rightarrow> False))))) | _ \<Rightarrow> False) \<longrightarrow> relTR (subst c (ks n)) (subst c result) \<and> is_value result \<and> (even n \<longrightarrow> result = K) \<and> (odd n \<longrightarrow> result = App K K)"
  sorry
end
