theory tree_height_Iteration_height1qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.bintree_Tree" "Why3STD.bintree_Size" "Why3STD.bintree_Height"
begin
datatype 'a cont = Id | Kleft "'a tree" "'a cont" | Kright "int" "'a cont"
datatype 'a what = Argument "'a tree" | Result "int"
definition is_id :: "'a cont \<Rightarrow> _"
  where "is_id k \<longleftrightarrow> (case k of (Id :: 'a cont) \<Rightarrow> True | _ \<Rightarrow> False)" for k
definition is_result :: "'a what \<Rightarrow> _"
  where "is_result w \<longleftrightarrow> (case w of Result _ \<Rightarrow> True | _ \<Rightarrow> False)" for w
fun evalk :: "'a cont \<Rightarrow> int \<Rightarrow> int"
  where "evalk (Id :: 'a cont) r = r" for r
      | "evalk (Kleft l k1) r = evalk k1 ((1 :: int) + max (height l) r)" for l k1 r
      | "evalk (Kright x k1) r = evalk k1 ((1 :: int) + max x r)" for x k1 r
definition evalw :: "'a what \<Rightarrow> int"
  where "evalw w = (case w of Argument t \<Rightarrow> height t | Result x \<Rightarrow> x)" for w
fun sizek :: "'a cont \<Rightarrow> int"
  where "sizek (Id :: 'a cont) = (0 :: int)"
      | "sizek (Kleft t k1) = (3 :: int) + (4 :: int) * bintree_Size.size t + sizek k1" for t k1
      | "sizek (Kright x k1) = (1 :: int) + sizek k1" for x k1
definition sizew :: "'a what \<Rightarrow> int"
  where "sizew w = (case w of Argument t \<Rightarrow> (1 :: int) + (4 :: int) * bintree_Size.size t | Result _ \<Rightarrow> (0 :: int))" for w
theorem height1'vc:
  fixes t :: "'a tree"
  shows "evalk (Id :: 'a cont) (evalw (Argument t)) = height t"
  and "\<forall>(k :: 'a cont) (w :: 'a what). evalk k (evalw w) = height t \<longrightarrow> (\<forall>(o1 :: bool). (if is_id k then o1 = (if is_result w then True else False) else o1 = False) \<longrightarrow> (if \<not>o1 = True then case k of (Id :: 'a cont) \<Rightarrow> (case w of Argument x \<Rightarrow> (case x of (Empty :: 'a tree) \<Rightarrow> ((0 :: int) \<le> sizek k + sizew w \<and> sizek k + sizew ((Result :: int \<Rightarrow> 'a what) (0 :: int)) < sizek k + sizew w) \<and> evalk k (evalw ((Result :: int \<Rightarrow> 'a what) (0 :: int))) = height t | Node x1 x2 x3 \<Rightarrow> ((0 :: int) \<le> sizek k + sizew w \<and> sizek (Kleft x3 k) + sizew (Argument x1) < sizek k + sizew w) \<and> evalk (Kleft x3 k) (evalw (Argument x1)) = height t) | Result x \<Rightarrow> False) | Kleft x x1 \<Rightarrow> (case w of Argument x2 \<Rightarrow> (case x2 of (Empty :: 'a tree) \<Rightarrow> ((0 :: int) \<le> sizek k + sizew w \<and> sizek k + sizew ((Result :: int \<Rightarrow> 'a what) (0 :: int)) < sizek k + sizew w) \<and> evalk k (evalw ((Result :: int \<Rightarrow> 'a what) (0 :: int))) = height t | Node x3 x4 x5 \<Rightarrow> ((0 :: int) \<le> sizek k + sizew w \<and> sizek (Kleft x5 k) + sizew (Argument x3) < sizek k + sizew w) \<and> evalk (Kleft x5 k) (evalw (Argument x3)) = height t) | Result x2 \<Rightarrow> ((0 :: int) \<le> sizek k + sizew w \<and> sizek (Kright x2 x1) + sizew (Argument x) < sizek k + sizew w) \<and> evalk (Kright x2 x1) (evalw (Argument x)) = height t) | Kright x x1 \<Rightarrow> (case w of Argument x2 \<Rightarrow> (case x2 of (Empty :: 'a tree) \<Rightarrow> ((0 :: int) \<le> sizek k + sizew w \<and> sizek k + sizew ((Result :: int \<Rightarrow> 'a what) (0 :: int)) < sizek k + sizew w) \<and> evalk k (evalw ((Result :: int \<Rightarrow> 'a what) (0 :: int))) = height t | Node x3 x4 x5 \<Rightarrow> ((0 :: int) \<le> sizek k + sizew w \<and> sizek (Kleft x5 k) + sizew (Argument x3) < sizek k + sizew w) \<and> evalk (Kleft x5 k) (evalw (Argument x3)) = height t) | Result x2 \<Rightarrow> ((0 :: int) \<le> sizek k + sizew w \<and> sizek x1 + sizew ((Result :: int \<Rightarrow> 'a what) ((1 :: int) + max x x2)) < sizek k + sizew w) \<and> evalk x1 (evalw ((Result :: int \<Rightarrow> 'a what) ((1 :: int) + max x x2))) = height t) else (case w of Result r \<Rightarrow> True | _ \<Rightarrow> False) \<and> (\<forall>(result :: int). (case w of Result r \<Rightarrow> result = r | _ \<Rightarrow> False) \<longrightarrow> result = height t)))"
  sorry
end
