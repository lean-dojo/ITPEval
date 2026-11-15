(*
Title: FriendshipTheory.thy
Author:Wenda Li
*)

theory FriendshipTheory 
  imports MoreGraph  "HOL-Number_Theory.Number_Theory"
begin

(*Proofs in this section are the common steps for both combinatorial and algebraic proofs for the
Friendship Theorem*)
section\<open>Common steps\<close>

definition (in valid_unSimpGraph) non_adj :: "'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "non_adj v v' \<equiv> v\<in>V \<and> v'\<in>V \<and> v\<noteq>v' \<and> \<not>adjacent v v'" 

lemma (in valid_unSimpGraph) no_quad:
  assumes "\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n"
  shows "\<not> (\<exists>v1 v2 v3 v4. v2\<noteq>v4 \<and> v1\<noteq>v3 \<and> adjacent v1 v2 \<and> adjacent v2 v3 \<and> adjacent v3 v4 
      \<and> adjacent v4 v1)"
  by sorry

lemma even_card_set: 
  assumes "finite A" and "\<forall>x\<in>A. f x\<in>A \<and> f x\<noteq> x \<and> f (f x)=x"
  shows "even(card A)" using assms
  by sorry

lemma (in valid_unSimpGraph) even_degree:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n" 
      and "finite E"
  shows "\<forall>v\<in>V. even(degree v G)"
  by sorry

lemma (in valid_unSimpGraph) degree_two_windmill:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n"
      and "finite E" and "card V\<ge>2"
  shows "(\<exists>v\<in>V. degree v G = 2) \<longleftrightarrow>(\<exists>v. \<forall>n\<in>V. n\<noteq>v \<longrightarrow> adjacent v n)"
  by sorry

lemma (in valid_unSimpGraph) regular:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n" 
      and "finite E" and "finite V" and "\<not>(\<exists>v\<in>V. degree v G = 2)"
  shows "\<exists>k. \<forall>v\<in>V. degree v G = k"
  by sorry

(*In this section, combinatorial proofs for the Friendship Theorem differ from the algebraic ones.
The main difference between these two approaches is that combinatorial proofs show Lemma 
exist_degree_two by counting the number of paths while algebraic proofs show it by computing
the eigenvalue of adjacency matrices.*)
section\<open>Exclusive steps for combinatorial proofs\<close>

fun (in valid_unSimpGraph) adj_path:: "'v \<Rightarrow> 'v list \<Rightarrow>bool" where
  "adj_path v [] =  (v\<in>V)" 
  | "adj_path v (u#us)= (adjacent v u \<and> adj_path u us)"

lemma (in valid_unSimpGraph) adj_path_butlast:
  "adj_path v ps \<Longrightarrow> adj_path v (butlast ps)"
  by sorry

lemma (in valid_unSimpGraph) adj_path_V:
  "adj_path v ps \<Longrightarrow> set ps \<subseteq> V"
  by sorry

lemma (in valid_unSimpGraph) adj_path_V':
  "adj_path v ps \<Longrightarrow> v\<in> V"
  by sorry

lemma (in valid_unSimpGraph) adj_path_app:
  "adj_path v ps \<Longrightarrow> ps\<noteq>[] \<Longrightarrow> adjacent (last ps) u \<Longrightarrow> adj_path v (ps@[u])"
  by sorry


lemma (in valid_unSimpGraph) adj_path_app':
  "adj_path v (ps @ [q] ) \<Longrightarrow> ps \<noteq> [] \<Longrightarrow> adjacent (last ps) q"
  by sorry

lemma card_partition':
  assumes "\<forall>v\<in>A. card {n. R v n} = k" "k>0" "finite A" 
      "\<forall>v1 v2. v1\<noteq>v2 \<longrightarrow> {n. R v1 n} \<inter> {n. R v2 n}={}"
  shows "card (\<Union>v\<in>A. {n. R v n}) = k * card A"
  by sorry

lemma (in valid_unSimpGraph) path_count:
  assumes k_adj:"\<And>v. v\<in>V \<Longrightarrow> card {n. adjacent v n} = k" and  "v\<in>V" and "finite V" and "k>0"
  shows "card {ps. length ps=l \<and> adj_path v ps}=k^l"
  by sorry

lemma (in valid_unSimpGraph) total_v_num:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n" 
      and "finite E" and "finite V" and "V\<noteq>{}" and " \<forall>v\<in>V. degree v G = k" and "k>0"
  shows "card V= k*k - k +1"
  by sorry

lemma rotate_eq:"rotate1 xs=rotate1 ys \<Longrightarrow> xs=ys" 
  by sorry
  

lemma rotate_diff:"rotate m xs=rotate n xs \<Longrightarrow>rotate (m-n) xs = xs"
  by sorry

lemma (in valid_unSimpGraph) exist_degree_two:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n"
      and "finite E" and "finite V" and "card V\<ge>2" 
  shows "\<exists>v\<in>V. degree v G = 2"
  by sorry

theorem (in valid_unSimpGraph) friendship_thm:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n"
      and "finite V" 
  shows "\<exists>v. \<forall>n\<in>V. n\<noteq>v \<longrightarrow> adjacent v n"    
  by sorry

end
