theory probability
  imports Main
begin

datatype 'a mylist = NilL | ConsL 'a "'a mylist"

primrec mapL :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mylist \<Rightarrow> 'b mylist" where
  "mapL f NilL        = NilL"
| "mapL f (ConsL x xs) = ConsL (f x) (mapL f xs)"

primrec fold_addL :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a mylist \<Rightarrow> 'a" where
  "fold_addL add z NilL        = z"
| "fold_addL add z (ConsL x xs) = add x (fold_addL add z xs)"

inductive InL :: "'a \<Rightarrow> 'a mylist \<Rightarrow> bool" where
  In_head : "InL x (ConsL x xs)"
| In_tail : "InL x xs \<Longrightarrow> InL x (ConsL y xs)"

inductive NoDupL :: "'a mylist \<Rightarrow> bool" where
  ND_nil  : "NoDupL NilL"
| ND_cons : "\<lbrakk>\<not> InL x xs; NoDupL xs\<rbrakk> \<Longrightarrow> NoDupL (ConsL x xs)"

type_synonym 'a event = "'a \<Rightarrow> bool"

definition ev_false :: "'a event" where "ev_false \<equiv> \<lambda>_. False"
definition ev_true  :: "'a event" where "ev_true  \<equiv> \<lambda>_. True"
definition ev_inter :: "'a event \<Rightarrow> 'a event \<Rightarrow> 'a event"
  where "ev_inter A B \<equiv> \<lambda>\<omega>. A \<omega> \<and> B \<omega>"
definition ev_union :: "'a event \<Rightarrow> 'a event \<Rightarrow> 'a event"
  where "ev_union A B \<equiv> \<lambda>\<omega>. A \<omega> \<or> B \<omega>"
definition ev_compl :: "'a event \<Rightarrow> 'a event"
  where "ev_compl A \<equiv> \<lambda>\<omega>. \<not> A \<omega>"
definition ev_diff  :: "'a event \<Rightarrow> 'a event \<Rightarrow> 'a event"
  where "ev_diff A B \<equiv> \<lambda>\<omega>. A \<omega> \<and> \<not> B \<omega>"

definition disjoint :: "'a event \<Rightarrow> 'a event \<Rightarrow> bool"
  where "disjoint A B \<equiv> \<forall>\<omega>. \<not> (A \<omega> \<and> B \<omega>)"

fun pairwise_disjoint :: "('a event) mylist \<Rightarrow> bool" where
  "pairwise_disjoint NilL = True"
| "pairwise_disjoint (ConsL _ NilL) = True"
| "pairwise_disjoint (ConsL A (ConsL B xs)) =
     (disjoint A B \<and>
      (\<forall>C. InL C (ConsL B xs) \<longrightarrow> disjoint A C) \<and>
      pairwise_disjoint (ConsL B xs))"

primrec bigUnion :: "('a event) mylist \<Rightarrow> 'a event" where
  "bigUnion NilL         = ev_false"
| "bigUnion (ConsL A xs) = ev_union A (bigUnion xs)"



lemma ev_inter_comm:
  "\<forall>\<omega>. ev_inter A B \<omega> \<longleftrightarrow> ev_inter B A \<omega>"
  sorry
lemma ev_union_comm:
  "\<forall>\<omega>. ev_union A B \<omega> \<longleftrightarrow> ev_union B A \<omega>"
  sorry
lemma ev_inter_assoc:
  "\<forall>\<omega>. ev_inter (ev_inter A B) C \<omega> \<longleftrightarrow> ev_inter A (ev_inter B C) \<omega>"
  sorry
lemma ev_union_assoc:
  "\<forall>\<omega>. ev_union (ev_union A B) C \<omega> \<longleftrightarrow> ev_union A (ev_union B C) \<omega>"
  sorry
lemma ev_inter_distrib_left:
  "\<forall>\<omega>. ev_inter A (ev_union B C) \<omega> \<longleftrightarrow> ev_union (ev_inter A B) (ev_inter A C) \<omega>"
  sorry

lemma disjoint_bigUnion:
  "(\<forall>C. InL C xs \<longrightarrow> disjoint A C) \<Longrightarrow> disjoint A (bigUnion xs)"
  sorry

locale probability_setup =
  fixes zero one :: "'r"
    and add       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "+R" 65)
    and opp       :: "'r \<Rightarrow> 'r"
    and mul       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "*R" 70)
    and prob      :: "('a \<Rightarrow> bool) \<Rightarrow> 'r"
    and cprob     :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'r"

  assumes
    add_comm      : "\<And>x y.   x +R y = y +R x"
    and add_assoc : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and add_zero  : "\<And>x.     x +R zero = x"
    and add_opp   : "\<And>x.     x +R opp x = zero"
    and mul_comm  : "\<And>x y.   x *R y = y *R x"
    and mul_assoc : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
    and mul_one   : "\<And>x.     x *R one = x"
    and dist_l    : "\<And>x y z. x *R (y +R z) = (x *R y) +R (x *R z)"
    and mul_zero  : "\<And>x.     x *R zero = zero"
    and opp_zero  : "opp zero = zero"
    and opp_opp   : "\<And>x.     opp (opp x) = x"
    and opp_mul_right : "\<And>x y. x *R opp y = opp (x *R y)"
    and opp_mul_left  : "\<And>x y. opp x *R y = opp (x *R y)"

    and prob_ext  : "\<And>A B. (\<forall>\<omega>. A \<omega> \<longleftrightarrow> B \<omega>) \<Longrightarrow> prob A = prob B"
    and prob_false_ax : "prob ev_false = zero"
    and prob_true_ax  : "prob ev_true  = one"
    and prob_union_ax :
          "\<And>A B. prob (ev_union A B) =
           prob A +R (prob B +R opp (prob (ev_inter A B)))"
    and prob_compl_ax : "\<And>A. prob (ev_compl A) = one +R opp (prob A)"
    and cprob_mul     : "\<And>A B. prob (ev_inter A B) = cprob A B *R prob B"
    and prob_union_disjoint :
          "\<And>A B. disjoint A B \<Longrightarrow>
           prob (ev_union A B) = prob A +R prob B"
    and disjoint_head_tail :
          "\<And>A xs. pairwise_disjoint (ConsL A xs) \<Longrightarrow>
           disjoint A (bigUnion xs)"
    and indep_compl_both_ax :
          "\<And>A B. prob (ev_inter A B) = prob A *R prob B \<Longrightarrow>
           prob (ev_inter (ev_compl A) (ev_compl B)) =
           prob (ev_compl A) *R prob (ev_compl B)"
    and inclusion_exclusion_three :
          "\<And>A B C.
           prob (ev_union (ev_union A B) C) =
           prob A +R (prob B +R (prob C +R
             opp (prob (ev_inter A B) +R
                  (prob (ev_inter A C) +R
                   (prob (ev_inter B C) +R
                    opp (prob (ev_inter (ev_inter A B) C)))))))"
begin





lemma zero_add: "zero +R x = x"
  sorry
lemma add_opp_comm: "opp x +R x = zero"
  sorry

lemma sub_of_eq: "a = b +R c \<Longrightarrow> c = a +R opp b"
  sorry




definition indep :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "indep A B \<equiv> prob (ev_inter A B) = prob A *R prob B"





lemma prob_union_comm:
  "prob (ev_union A B) = prob (ev_union B A)"
  sorry
lemma prob_union_idem:
  "prob (ev_union A A) = prob A"
  sorry




lemma prob_diff:
  "prob (ev_diff A B) = prob A +R opp (prob (ev_inter A B))"
  sorry




lemma bayes_symm:
  "cprob A B *R prob B = cprob B A *R prob A"
  sorry




lemma law_total_prob:
  "prob A =
   cprob A B *R prob B +R cprob A (ev_compl B) *R prob (ev_compl B)"
  sorry




lemma prob_union_indep:
  "indep A B \<Longrightarrow>
   prob (ev_union A B) =
   prob A +R (prob B +R opp (prob A *R prob B))"
  sorry




lemma indep_symm: "indep A B \<Longrightarrow> indep B A"
  sorry
lemma indep_compl_right: "indep A B \<Longrightarrow> indep A (ev_compl B)"
  sorry
lemma indep_compl_left: "indep A B \<Longrightarrow> indep (ev_compl A) B"
  sorry
lemma indep_compl_both: "indep A B \<Longrightarrow> indep (ev_compl A) (ev_compl B)"
  sorry




lemma prob_bigUnion_disjoint:
  "pairwise_disjoint xs \<Longrightarrow>
   prob (bigUnion xs) = fold_addL (+R) zero (mapL prob xs)"
  sorry




lemma prob_bigUnion_disjoint_zero:
  "pairwise_disjoint xs \<Longrightarrow>
   (\<forall>A. InL A xs \<longrightarrow> prob A = zero) \<Longrightarrow>
   prob (bigUnion xs) = zero"
  sorry
end

end
