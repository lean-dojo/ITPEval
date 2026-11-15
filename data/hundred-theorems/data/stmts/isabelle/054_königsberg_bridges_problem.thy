(*
Title:KoenigsbergBridge.thy
Author:Wenda Li
*)

theory KoenigsbergBridge imports MoreGraph
begin

section\<open>Definition of Eulerian trails and circuits\<close>

definition (in valid_unMultigraph) is_Eulerian_trail:: "'v\<Rightarrow>('v,'w) path\<Rightarrow>'v\<Rightarrow> bool" where
  "is_Eulerian_trail v ps v'\<equiv> is_trail v ps v' \<and> edges (rem_unPath ps G) = {}"

definition (in valid_unMultigraph) is_Eulerian_circuit:: "'v \<Rightarrow> ('v,'w) path \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_Eulerian_circuit v ps v'\<equiv> (v=v') \<and> (is_Eulerian_trail v ps v')"

section\<open>Necessary conditions for Eulerian trails and circuits\<close>

lemma (in valid_unMultigraph) euclerian_rev:
  "is_Eulerian_trail v' (rev_path ps) v=is_Eulerian_trail v ps v' "
  by sorry

(*Necessary conditions for Eulerian circuits*)
theorem (in valid_unMultigraph) euclerian_cycle_ex:
  assumes "is_Eulerian_circuit v ps v'" "finite V" "finite E"
  shows "\<forall>v\<in>V. even (degree v G)"
  by sorry

(*Necessary conditions for Eulerian trails*)
theorem (in valid_unMultigraph) euclerian_path_ex:
  assumes "is_Eulerian_trail v ps v'" "finite V" "finite E"
  shows "(\<forall>v\<in>V. even (degree v G)) \<or> (num_of_odd_nodes G =2)"
  by sorry

section\<open>Specific case of the Konigsberg Bridge Problem\<close>

(*to denote the four landmasses*)
datatype kon_node = a | b | c | d

(*to denote the seven bridges*)
datatype kon_bridge = ab1 | ab2 | ac1 | ac2 | ad1 | bd1 | cd1

definition kon_graph :: "(kon_node,kon_bridge) graph" where
  "kon_graph\<equiv>\<lparr>nodes={a,b,c,d},
              edges={(a,ab1,b), (b,ab1,a),
                     (a,ab2,b), (b,ab2,a),
                     (a,ac1,c), (c,ac1,a),
                     (a,ac2,c), (c,ac2,a),
                     (a,ad1,d), (d,ad1,a),
                     (b,bd1,d), (d,bd1,b),
                     (c,cd1,d), (d,cd1,c)} \<rparr>"

instantiation kon_node :: enum
begin
definition [simp]:  "enum_class.enum =[a,b,c,d]"
definition  [simp]: "enum_class.enum_all P \<longleftrightarrow> P a \<and> P b \<and> P c \<and> P d"
definition   [simp]:"enum_class.enum_ex P \<longleftrightarrow> P a \<or> P b \<or> P c \<or> P d"
instance proof qed (auto,(case_tac x,auto)+)
end

instantiation kon_bridge :: enum
begin
definition [simp]:"enum_class.enum =[ab1,ab2,ac1,ac2,ad1,cd1,bd1]"
definition  [simp]:"enum_class.enum_all P \<longleftrightarrow> P ab1 \<and> P ab2 \<and> P ac1 \<and> P ac2 \<and> P ad1  \<and> P bd1
    \<and> P cd1"
definition   [simp]:"enum_class.enum_ex P \<longleftrightarrow>  P ab1 \<or> P ab2 \<or> P ac1 \<or> P ac2 \<or> P ad1  \<or> P bd1
    \<or> P cd1"
instance proof qed (auto,(case_tac x,auto)+)
end

interpretation   kon_graph: valid_unMultigraph kon_graph
proof (unfold_locales)
  show "fst ` edges kon_graph \<subseteq> nodes kon_graph" by eval
next
  show "snd ` snd ` edges kon_graph \<subseteq> nodes kon_graph"  by eval
next
  have " \<forall>v w u'. ((v, w, u') \<in> edges kon_graph) = ((u', w, v) \<in> edges kon_graph)"
    by eval
  thus "\<And>v w u'. ((v, w, u') \<in> edges kon_graph) = ((u', w, v) \<in> edges kon_graph)" by simp
next
  have "\<forall>v w. (v, w, v) \<notin> edges kon_graph"  by eval
  thus "\<And>v w. (v, w, v) \<notin> edges kon_graph" by simp
qed

(*The specific case of the Konigsberg Bridge Problem does not have a solution*)
theorem "\<not>kon_graph.is_Eulerian_trail v1 p v2"
  by sorry

section\<open>Sufficient conditions for Eulerian trails and circuits\<close>

lemma (in valid_unMultigraph) eulerian_cons:
  assumes
    "valid_unMultigraph.is_Eulerian_trail (del_unEdge v0 w v1 G) v1 ps v2"
    "(v0,w,v1)\<in> E"
  shows "is_Eulerian_trail v0 ((v0,w,v1)#ps) v2"
  by sorry

lemma (in valid_unMultigraph) eulerian_cons':
  assumes
    "valid_unMultigraph.is_Eulerian_trail (del_unEdge v2 w v3 G) v1 ps v2"
    "(v2,w,v3)\<in> E"
  shows "is_Eulerian_trail v1 (ps@[(v2,w,v3)]) v3"
  by sorry

lemma eulerian_split:
  assumes "nodes G1 \<inter> nodes G2 = {}" "edges G1 \<inter> edges G2={}"
    "valid_unMultigraph G1" "valid_unMultigraph G2"
    "valid_unMultigraph.is_Eulerian_trail  G1 v1 ps1 v1'"
    "valid_unMultigraph.is_Eulerian_trail  G2 v2 ps2 v2'"
  shows "valid_unMultigraph.is_Eulerian_trail \<lparr>nodes=nodes G1 \<union> nodes G2,
          edges=edges G1 \<union> edges G2 \<union> {(v1',w,v2),(v2,w,v1')}\<rparr> v1 (ps1@(v1',w,v2)#ps2) v2'"
  by sorry

lemma (in valid_unMultigraph) eulerian_sufficient:
  assumes "finite V" "finite E" "connected" "V\<noteq>{}"
  shows "num_of_odd_nodes G = 2 \<Longrightarrow>
      (\<exists>v\<in>V.\<exists>v'\<in>V.\<exists>ps. odd(degree v G)\<and>odd(degree v' G)\<and>(v\<noteq>v')\<and>is_Eulerian_trail v ps v')"
      and "num_of_odd_nodes G=0 \<Longrightarrow> (\<forall>v\<in>V.\<exists>ps. is_Eulerian_circuit v ps v)"
  by sorry
end
