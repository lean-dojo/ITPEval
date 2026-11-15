theory imp_ConcreteInterpreter_interp_exprqtvc
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/imp_Syntax" "../../lib/isabelle/imp_ConcreteSemantics" "../../lib/isabelle/dict_Imperative"
begin
typedecl  env
theorem interp_expr'vc:
  fixes e :: "expr"
  fixes env1 :: "(program_var, int) t"
  shows "case e of Elit n \<Rightarrow> eval_expr (model1 env1) e (Enormal n) | Evar x \<Rightarrow> (\<forall>(result :: int). (case get env1 x of None \<Rightarrow> False | Some v \<Rightarrow> result = v) \<longrightarrow> eval_expr (model1 env1) e (Enormal result)) \<and> (get env1 x = None \<longrightarrow> eval_expr (model1 env1) e Eunbound_var) | Esub e1 e2 \<Rightarrow> (case e of Elit _ \<Rightarrow> False | Evar _ \<Rightarrow> False | Esub f f1 \<Rightarrow> f = e2 \<or> f1 = e2) \<and> (\<forall>(o1 :: int). eval_expr (model1 env1) e2 (Enormal o1) \<longrightarrow> (case e of Elit _ \<Rightarrow> False | Evar _ \<Rightarrow> False | Esub f f1 \<Rightarrow> f = e1 \<or> f1 = e1) \<and> (\<forall>(o2 :: int). eval_expr (model1 env1) e1 (Enormal o2) \<longrightarrow> eval_expr (model1 env1) e (Enormal (o2 - o1))) \<and> (eval_expr (model1 env1) e1 Eunbound_var \<longrightarrow> eval_expr (model1 env1) e Eunbound_var)) \<and> (eval_expr (model1 env1) e2 Eunbound_var \<longrightarrow> eval_expr (model1 env1) e Eunbound_var)"
  sorry
end
