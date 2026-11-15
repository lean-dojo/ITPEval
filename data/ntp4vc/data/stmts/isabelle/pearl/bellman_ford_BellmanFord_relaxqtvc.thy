theory bellman_ford_BellmanFord_relaxqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_IntInf" "Why3STD.map_Const" "./bellman_ford_Graph"
begin
typedecl  set
consts to_fset :: "set \<Rightarrow> (vertex \<times> vertex) fset"
consts choose1 :: "set \<Rightarrow> vertex \<times> vertex"
axiomatization where choose'spec:   "choose1 s |\<in>| to_fset s"
 if "\<not>to_fset s = fempty"
  for s :: "set"
typedecl 'a t
consts contents :: "'a t \<Rightarrow> vertex \<Rightarrow> 'a"
consts create :: "'a \<Rightarrow> 'a t"
axiomatization where create'spec:   "contents (create x) = (const :: 'a \<Rightarrow> vertex \<Rightarrow> 'a) x"
  for x :: "'a"
consts mixfix_lbrb :: "'a t \<Rightarrow> vertex \<Rightarrow> 'a"
axiomatization where mixfix_lbrb'spec:   "mixfix_lbrb m k = contents m k"
  for m :: "'a t"
  and k :: "vertex"
consts mixfix_lblsmnrb :: "'a t \<Rightarrow> vertex \<Rightarrow> 'a \<Rightarrow> 'a t"
axiomatization where mixfix_lblsmnrb'spec:   "contents (mixfix_lblsmnrb m k v) = (contents m)(k := v)"
  for m :: "'a t"
  and k :: "vertex"
  and v :: "'a"
typedecl  distmap
definition inv1 :: "int_IntInf.t t \<Rightarrow> int \<Rightarrow> (vertex \<times> vertex) fset \<Rightarrow> _"
  where "inv1 m pass via \<longleftrightarrow> (\<forall>(v :: vertex). v |\<in>| vertices \<longrightarrow> (case mixfix_lbrb m v of Finite n \<Rightarrow> (\<exists>(l :: vertex list). path s l v \<and> path_weight l v = n) \<and> (\<forall>(l :: vertex list). path s l v \<longrightarrow> int (length l) < pass \<longrightarrow> n \<le> path_weight l v) \<and> (\<forall>(u :: vertex) (l :: vertex list). path s l u \<longrightarrow> int (length l) < pass \<longrightarrow> (u, v) |\<in>| via \<longrightarrow> n \<le> path_weight l u + weight u v) | Infinite \<Rightarrow> (\<forall>(l :: vertex list). path s l v \<longrightarrow> pass \<le> int (length l)) \<and> (\<forall>(u :: vertex). (u, v) |\<in>| via \<longrightarrow> (\<forall>(lu :: vertex list). path s lu u \<longrightarrow> pass \<le> int (length lu)))))" for m pass via
definition inv2 :: "int_IntInf.t t \<Rightarrow> (vertex \<times> vertex) fset \<Rightarrow> _"
  where "inv2 m via \<longleftrightarrow> (\<forall>(u :: vertex) (v :: vertex). (u, v) |\<in>| via \<longrightarrow> le (mixfix_lbrb m v) (add (mixfix_lbrb m u) (Finite (weight u v))))" for m via
theorem relax'vc:
  fixes pass :: "int"
  fixes u :: "vertex"
  fixes v :: "vertex"
  fixes via :: "(vertex \<times> vertex) fset"
  fixes m :: "int_IntInf.t t"
  assumes fact0: "(1 :: int) \<le> pass"
  assumes fact1: "(u, v) |\<in>| edges"
  assumes fact2: "\<not>(u, v) |\<in>| via"
  assumes fact3: "inv1 m pass via"
  shows "let o1 :: int_IntInf.t = mixfix_lbrb m u in o1 = contents m u \<longrightarrow> (let n :: int_IntInf.t = add o1 (Finite (weight u v)); o2 :: int_IntInf.t = mixfix_lbrb m v in o2 = contents m v \<longrightarrow> (if lt n o2 then inv1 (mixfix_lblsmnrb m v n) pass (finsert (u, v) via) else inv1 m pass (finsert (u, v) via)))"
  sorry
end
