theory vacid_0_red_black_trees_RedBlackTree_lbalanceqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  key
typedecl  "value"
datatype  color = Red | Black
datatype  tree = Leaf | Node "color" "tree" "int" "int" "tree"
fun memt :: "tree \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "memt Leaf k v = False" for k v
      | "memt (Node x l k' v' r) k v = (k = k' \<and> v = v' \<or> memt l k v \<or> memt r k v)" for x l k' v' r k v
definition lt_tree :: "int \<Rightarrow> tree \<Rightarrow> _"
  where "lt_tree x t \<longleftrightarrow> (\<forall>(k :: int) (v :: int). memt t k v \<longrightarrow> k < x)" for x t
definition gt_tree :: "int \<Rightarrow> tree \<Rightarrow> _"
  where "gt_tree x t \<longleftrightarrow> (\<forall>(k :: int) (v :: int). memt t k v \<longrightarrow> x < k)" for x t
fun bst :: "tree \<Rightarrow> _"
  where "bst Leaf = True"
      | "bst (Node x l k x0 r) = (bst l \<and> bst r \<and> lt_tree k l \<and> gt_tree k r)" for x l k x0 r
definition is_not_red :: "tree \<Rightarrow> _"
  where "is_not_red t \<longleftrightarrow> (case t of Node Red _ _ _ _ \<Rightarrow> False | Leaf \<Rightarrow> True | Node Black _ _ _ _ \<Rightarrow> True)" for t
fun rbtree :: "int \<Rightarrow> tree \<Rightarrow> _"
  where "rbtree n Leaf = (n = (0 :: int))" for n
      | "rbtree n (Node Red l x x0 r) = (rbtree n l \<and> rbtree n r \<and> is_not_red l \<and> is_not_red r)" for n l x x0 r
      | "rbtree n (Node Black l x x0 r) = (rbtree (n - (1 :: int)) l \<and> rbtree (n - (1 :: int)) r)" for n l x x0 r
definition almost_rbtree :: "int \<Rightarrow> tree \<Rightarrow> _"
  where "almost_rbtree n t \<longleftrightarrow> (case t of Leaf \<Rightarrow> n = (0 :: int) | Node Red l _ _ r \<Rightarrow> rbtree n l \<and> rbtree n r | Node Black l _ _ r \<Rightarrow> rbtree (n - (1 :: int)) l \<and> rbtree (n - (1 :: int)) r)" for n t
theorem lbalance'vc:
  fixes k :: "int"
  fixes l :: "tree"
  fixes r :: "tree"
  fixes v :: "int"
  assumes fact0: "lt_tree k l"
  assumes fact1: "gt_tree k r"
  assumes fact2: "bst l"
  assumes fact3: "bst r"
  shows "case l of Node Red (Node Red a kx vx b) ky vy c \<Rightarrow> True | Node Red a kx vx (Node Red b ky vy c) \<Rightarrow> True | _ \<Rightarrow> True"
  and "\<forall>(result :: tree). (case l of Node Red (Node Red a kx vx b) ky vy c \<Rightarrow> result = Node Red (Node Black a kx vx b) ky vy (Node Black c k v r) | Node Red a kx vx (Node Red b ky vy c) \<Rightarrow> result = Node Red (Node Black a kx vx b) ky vy (Node Black c k v r) | _ \<Rightarrow> result = Node Black l k v r) \<longrightarrow> bst result \<and> (\<forall>(n :: int). almost_rbtree n l \<longrightarrow> rbtree n r \<longrightarrow> rbtree (n + (1 :: int)) result) \<and> (\<forall>(k' :: int) (v' :: int). memt result k' v' \<longleftrightarrow> (if k' = k then v' = v else memt l k' v' \<or> memt r k' v'))"
  sorry
end
