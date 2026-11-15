theory supinf
  imports Main
begin

locale complete_ordered_field =
  fixes zero_nat  :: "'n"
    and succ      :: "'n \<Rightarrow> 'n"
    and nat_le    :: "'n \<Rightarrow> 'n \<Rightarrow> bool"
    and zero one  :: "'r"
    and add       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "+R" 65)
    and mul       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "*R" 70)
    and opp inv   :: "'r \<Rightarrow> 'r"
    and rle       :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "\<le>R" 50)
    and rlt       :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "<R" 50)
    and rabs      :: "'r \<Rightarrow> 'r"
    and inr       :: "'n \<Rightarrow> 'r"
  assumes nat_le_refl   : "\<And>n. nat_le n n"
    and   le_succ_of_le : "\<And>n m. nat_le n m \<Longrightarrow> nat_le n (succ m)"
    and   le_succ       : "\<And>n. nat_le n (succ n)"
    and   add_comm      : "\<And>x y. x +R y = y +R x"
    and   add_assoc     : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and   add_zero      : "\<And>x. x +R zero = x"
    and   add_opp       : "\<And>x. opp x +R x = zero"
    and   mul_comm      : "\<And>x y. x *R y = y *R x"
    and   mul_assoc     : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
    and   mul_one       : "\<And>x. x *R one = x"
    and   dist_l        : "\<And>x y z. x *R (y +R z) = (x *R y) +R (x *R z)"
    and   sub_zero      : "\<And>x. x +R opp zero = x"
    and   rle_refl      : "\<And>x. x \<le>R x"
    and   rle_trans     : "\<And>x y z. x \<le>R y \<Longrightarrow> y \<le>R z \<Longrightarrow> x \<le>R z"
    and   rle_antisym   : "\<And>x y. x \<le>R y \<Longrightarrow> y \<le>R x \<Longrightarrow> x = y"
    and   rlt_def       : "\<And>x y. (x <R y) \<longleftrightarrow> (x \<le>R y \<and> x \<noteq> y)"
    and   rle_abs       : "\<And>x. x +R opp zero \<le>R rabs x"
    and   rinv_pos      : "\<And>x. zero <R x \<Longrightarrow> zero <R inv x"
    and   rplus_le_compat_l : "\<And>x y z. y \<le>R z \<Longrightarrow> x +R y \<le>R x +R z"
    and   rinv_involutive    : "\<And>x. zero <R x \<Longrightarrow> inv (inv x) = x"
    and   inr_pos       : "\<And>n. zero <R inr (succ n)"
    and   inr_le        : "\<And>m n. nat_le m n \<Longrightarrow> inr m \<le>R inr n"
    and   inr_zero      : "inr zero_nat = zero"
    and   inr_succ      : "\<And>n. inr (succ n) = inr n +R one"
    and   rtotal_order  : "\<And>x y. (x <R y) \<or> x = y \<or> (y <R x)"
    and   rle_inv_contravar :
            "\<And>a b. zero <R a \<Longrightarrow> zero <R b \<Longrightarrow> a \<le>R b \<Longrightarrow> inv b \<le>R inv a"
    and   eps_between   :
            "\<And>x y. x <R y \<Longrightarrow> \<exists>eps. zero <R eps \<and> x +R eps <R y"
    and   archimedean   : "\<And>x. \<exists>n. x \<le>R inr n"
    and   completeness  :
            "\<And>A. (\<exists>ub. \<forall>a. A a \<longrightarrow> ub \<le>R a) \<Longrightarrow>
              \<exists>sup. (\<forall>a. A a \<longrightarrow> a \<le>R sup) \<and>
                    (\<forall>y. (\<forall>a. A a \<longrightarrow> a \<le>R y) \<longrightarrow> sup \<le>R y)"
begin





lemma add_opp_r: "x +R opp x = zero"
  sorry
lemma rlt_le: "x <R y \<Longrightarrow> x \<le>R y"
  sorry
lemma rlt_ne: "x <R y \<Longrightarrow> x \<noteq> y"
  sorry
lemma rlt_intro: "x \<le>R y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x <R y"
  sorry




definition up_bounds :: "('r \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool"
  where "up_bounds A x \<equiv> \<forall>a. A a \<longrightarrow> a \<le>R x"

definition is_maximum :: "'r \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_maximum a A \<equiv> A a \<and> up_bounds A a"

definition low_bounds :: "('r \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool"
  where "low_bounds A x \<equiv> \<forall>a. A a \<longrightarrow> x \<le>R a"

definition is_inf :: "'r \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_inf x A \<equiv> is_maximum x (low_bounds A)"

definition limit :: "('n \<Rightarrow> 'r) \<Rightarrow> 'r \<Rightarrow> bool"
  where "limit u l \<equiv>
    \<forall>eps. zero <R eps \<longrightarrow>
      (\<exists>N. \<forall>n. nat_le N n \<longrightarrow> rabs (u n +R opp l) \<le>R eps)"





lemma add_sub_cancel_r: "a +R (b +R opp a) = b"
  sorry




lemma rabs_pos: "t \<le>R rabs t"
  sorry




lemma unique_max:
  assumes "is_maximum x A" "is_maximum y A"
  shows "x = y"
  sorry




lemma inf_lt:
  assumes hinf: "is_inf x A" and hlt: "x <R y"
  shows "\<exists>a. A a \<and> a <R y"
  sorry




lemma le_of_le_add_eps:
  assumes H: "\<forall>eps. zero <R eps \<longrightarrow> y \<le>R x +R eps"
  shows "y \<le>R x"
  sorry




lemma le_lim:
  assumes hlim : "limit u x"
      and hle  : "\<forall>n. y \<le>R u n"
  shows "y \<le>R x"
  sorry




lemma inv_succ_pos: "zero <R inv (inr (succ n))"
  sorry




lemma limit_inv_succ:
  assumes heps: "zero <R eps"
  shows "\<exists>N. \<forall>n. nat_le N n \<longrightarrow> inv (inr (succ n)) \<le>R eps"
  sorry
end

end
