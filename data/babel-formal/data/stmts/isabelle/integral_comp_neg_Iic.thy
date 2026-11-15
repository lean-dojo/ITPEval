theory integral_comp_neg_Iic
  imports Main
begin

locale integrals_setup =
  fixes zero one  :: "'r"
    and add       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "+R" 65)
    and opp       :: "'r \<Rightarrow> 'r"
    and mul       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "*R" 70)
    and leR       :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "\<le>R" 50)
    and ltR       :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "<R" 50)
    and absR      :: "'r \<Rightarrow> 'r"
    and sigma     :: "('r \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> 'r) \<Rightarrow> 'r"

  assumes
    add_comm      : "\<And>x y.   x +R y = y +R x"
    and add_assoc : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and add_zero  : "\<And>x.     x +R zero = x"
    and add_opp   : "\<And>x.     opp x +R x = zero"
    and add_right_cancel : "\<And>x y z. x +R z = y +R z \<Longrightarrow> x = y"
    and mul_comm  : "\<And>x y.   x *R y = y *R x"
    and mul_assoc : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
    and mul_one   : "\<And>x.     x *R one = x"
    and dist_l    : "\<And>x y z. x *R (y +R z) = (x *R y) +R (x *R z)"
    and opp_inv   : "\<And>x.     opp (opp x) = x"
    and add_le_compat : "\<And>x y z. x \<le>R y \<Longrightarrow> (x +R z) \<le>R (y +R z)"
    and le_opp    : "\<And>x y.   x \<le>R y \<Longrightarrow> opp y \<le>R opp x"
    and le_antisymm : "\<And>x y. x \<le>R y \<Longrightarrow> y \<le>R x \<Longrightarrow> x = y"
    and lt_opp    : "\<And>x y.   x <R y \<Longrightarrow> opp y <R opp x"
    and le_refl   : "\<And>x.     x \<le>R x"
    and le_trans  : "\<And>x y z. x \<le>R y \<Longrightarrow> y \<le>R z \<Longrightarrow> x \<le>R z"
    and le_total  : "\<And>x y.   x \<le>R y \<or> y \<le>R x"
    and lt_def    : "\<And>x y.   (x <R y) \<longleftrightarrow> (x \<le>R y \<and> x \<noteq> y)"
    and abs_pos   : "\<And>x.     zero \<le>R x \<Longrightarrow> absR x = x"
    and abs_neg   : "\<And>x.     x \<le>R zero \<Longrightarrow> absR x = opp x"
    and abs_nonneg : "\<And>x.    zero \<le>R absR x"
    and abs_opp   : "\<And>x.     absR (opp x) = absR x"
    and abs_triangle : "\<And>x y. absR (x +R y) \<le>R (absR x +R absR y)"

    and sigma_mul_const : "\<And>D f c. sigma D (\<lambda>x. c *R f x) = c *R sigma D f"
    and sigma_congr : "\<And>D f g. (\<forall>x. D x \<longrightarrow> f x = g x) \<Longrightarrow> sigma D f = sigma D g"
    and sigma_zero  : "\<And>D.     sigma D (\<lambda>_. zero) = zero"
    and sigma_add   : "\<And>D f g. sigma D (\<lambda>x. f x +R g x) = sigma D f +R sigma D g"
    and sigma_union_disjoint :
          "\<And>D E f. (\<forall>x. D x \<longrightarrow> E x \<longrightarrow> False) \<Longrightarrow>
            sigma (\<lambda>x. D x \<or> E x) f = sigma D f +R sigma E f"
    and sigma_le    : "\<And>D f g. (\<forall>x. D x \<longrightarrow> f x \<le>R g x) \<Longrightarrow> sigma D f \<le>R sigma D g"
    and sigma_dom_congr :
          "\<And>D E f. (\<forall>x. D x \<longleftrightarrow> E x) \<Longrightarrow> sigma D f = sigma E f"
begin





definition Iic :: "'r \<Rightarrow> 'r \<Rightarrow> bool" where "Iic c x \<equiv> x \<le>R c"
definition Ioi :: "'r \<Rightarrow> 'r \<Rightarrow> bool" where "Ioi c x \<equiv> c <R x"
definition Iio :: "'r \<Rightarrow> 'r \<Rightarrow> bool" where "Iio c x \<equiv> x <R c"

definition preimage :: "('r \<Rightarrow> 'r) \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool"
  where "preimage g D x \<equiv> D (g x)"





lemma add_opp_r: "x +R opp x = zero"
  sorry




lemma lt_irrefl: "\<not> (x <R x)"
  sorry
lemma lt_trans_strict: "x <R y \<Longrightarrow> y <R z \<Longrightarrow> x <R z"
  sorry




lemma preimage_union:
  "preimage g (\<lambda>x. D x \<or> E x) x \<longleftrightarrow> preimage g D x \<or> preimage g E x"
  sorry
lemma preimage_inter:
  "preimage g (\<lambda>x. D x \<and> E x) x \<longleftrightarrow> preimage g D x \<and> preimage g E x"
  sorry
lemma preimage_neg_Ioi: "preimage opp (Ioi c) x \<longleftrightarrow> x <R opp c"
  sorry
lemma preimage_neg_Iic: "preimage opp (Iic c) x \<longleftrightarrow> opp c \<le>R x"
  sorry
lemma preimage_comp:
  "preimage g (preimage h D) x \<longleftrightarrow> preimage (\<lambda>x. h (g x)) D x"
  sorry




lemma integral_neg: "sigma D (\<lambda>x. opp (f x)) = opp (sigma D f)"
  sorry
lemma integral_sub:
  "sigma D (\<lambda>x. f x +R opp (g x)) = sigma D f +R opp (sigma D g)"
  sorry




lemma sigma_empty: "sigma (\<lambda>_. False) f = zero"
  sorry




lemma sigma_bilinear:
  "sigma D (\<lambda>x. (c *R f x) +R (d *R g x)) =
   (c *R sigma D f) +R (d *R sigma D g)"
  sorry




lemma sigma_le_monotone:
  "(\<forall>x. D x \<longrightarrow> f x \<le>R g x) \<Longrightarrow> sigma D f \<le>R sigma D g"
  sorry
lemma sigma_nonneg:
  "(\<forall>x. D x \<longrightarrow> zero \<le>R f x) \<Longrightarrow> zero \<le>R sigma D f"
  sorry




lemma sigma_split:
  "sigma D f =
   sigma (\<lambda>x. D x \<and> P x) f +R sigma (\<lambda>x. D x \<and> \<not> P x) f"
  sorry




lemma sigma_preimage_neg_Ioi:
  "sigma (preimage opp (Ioi c)) f = sigma (Iio (opp c)) f"
  sorry




lemma sigma_abs_bound:
  "absR (sigma D f) \<le>R sigma D (\<lambda>x. absR (f x))"
  sorry
end

end
