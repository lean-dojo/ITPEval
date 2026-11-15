theory polynomial
  imports Main
begin






datatype mynat = Nat_O | Nat_S mynat

fun mynat_add :: "mynat \<Rightarrow> mynat \<Rightarrow> mynat" where
  "mynat_add Nat_O m = m"
| "mynat_add (Nat_S n') m = Nat_S (mynat_add n' m)"

lemma mynat_add_O_left: "mynat_add Nat_O m = m"
  sorry
lemma mynat_add_S_left: "mynat_add (Nat_S n) m = Nat_S (mynat_add n m)"
  sorry
inductive mynat_le :: "mynat \<Rightarrow> mynat \<Rightarrow> bool" where
  le_n : "mynat_le n n"
| le_S : "mynat_le n m \<Longrightarrow> mynat_le n (Nat_S m)"

lemma mynat_zero_le: "mynat_le Nat_O n"
  sorry
lemma mynat_add_zero_r: "mynat_add n Nat_O = n"
  sorry
lemma mynat_succ_le_succ: "mynat_le n m \<Longrightarrow> mynat_le (Nat_S n) (Nat_S m)"
  sorry
lemma mynat_add_S_r: "mynat_add m (Nat_S n) = Nat_S (mynat_add m n)"
  sorry
lemma mynat_add_comm: "mynat_add n m = mynat_add m n"
  sorry




datatype 'a mylist = NilL | ConsL 'a "'a mylist"

inductive InL :: "'a \<Rightarrow> 'a mylist \<Rightarrow> bool" where
  In_head : "InL x (ConsL x xs)"
| In_tail : "InL x xs \<Longrightarrow> InL x (ConsL y xs)"

inductive NoDupL :: "'a mylist \<Rightarrow> bool" where
  ND_nil  : "NoDupL NilL"
| ND_cons : "\<not> InL x xs \<Longrightarrow> NoDupL xs \<Longrightarrow> NoDupL (ConsL x xs)"

fun lengthL :: "'a mylist \<Rightarrow> mynat" where
  "lengthL NilL = Nat_O"
| "lengthL (ConsL _ rest) = Nat_S (lengthL rest)"





locale polynomial_setup =
  fixes zero_r :: "'r"
    and one_r  :: "'r"
    and opp_r  :: "'r \<Rightarrow> 'r"
    and add_r  :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl \<open>+R\<close> 65)
    and mul_r  :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl \<open>*R\<close> 70)
    and zero_p :: "'p"
    and one_p  :: "'p"
    and opp_p  :: "'p \<Rightarrow> 'p"
    and add_p  :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"  (infixl \<open>+P\<close> 65)
    and mul_p  :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"  (infixl \<open>*P\<close> 70)
    and degree   :: "'p \<Rightarrow> mynat"
    and monomial :: "mynat \<Rightarrow> 'r \<Rightarrow> 'p"
    and eval     :: "'p \<Rightarrow> 'r \<Rightarrow> 'r"
  assumes
    r_one_neq_zero  : "one_r \<noteq> zero_r"
  and r_add_comm    : "\<And>x y.   x +R y = y +R x"
  and r_add_assoc   : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
  and r_add_zero    : "\<And>x.     x +R zero_r = x"
  and r_add_opp     : "\<And>x.     x +R opp_r x = zero_r"
  and r_mul_comm    : "\<And>x y.   x *R y = y *R x"
  and r_mul_assoc   : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
  and r_mul_one     : "\<And>x.     x *R one_r = x"
  and r_dist_l      : "\<And>x y z. x *R (y +R z) = (x *R y) +R (x *R z)"
  and r_mul_zero    : "\<And>x.     x *R zero_r = zero_r"
  and r_no_zero_div : "\<And>x y.   x *R y = zero_r \<Longrightarrow> x = zero_r \<or> y = zero_r"
  and p_one_neq_zero : "one_p \<noteq> zero_p"
  and p_add_comm    : "\<And>x y.   x +P y = y +P x"
  and p_add_assoc   : "\<And>x y z. (x +P y) +P z = x +P (y +P z)"
  and p_add_zero    : "\<And>x.     x +P zero_p = x"
  and p_add_opp     : "\<And>x.     x +P opp_p x = zero_p"
  and p_mul_comm    : "\<And>x y.   x *P y = y *P x"
  and p_mul_assoc   : "\<And>x y z. (x *P y) *P z = x *P (y *P z)"
  and p_mul_one     : "\<And>x.     x *P one_p = x"
  and p_dist_l      : "\<And>x y z. x *P (y +P z) = (x *P y) +P (x *P z)"
  and p_mul_zero    : "\<And>x.     x *P zero_p = zero_p"
  and p_no_zero_div : "\<And>x y.   x *P y = zero_p \<Longrightarrow> x = zero_p \<or> y = zero_p"
  and deg_zero      : "degree zero_p = Nat_O"
  and eval_add      : "\<And>p q x. eval (p +P q) x = eval p x +R eval q x"
  and eval_mul      : "\<And>p q x. eval (p *P q) x = eval p x *R eval q x"
  and eval_C_ax     : "\<And>c x.   eval (monomial Nat_O c) x = c"
  and eval_X_ax     : "\<And>x.     eval (monomial (Nat_S Nat_O) one_r) x = x"
  and deg_C_ax      : "\<And>c.     c \<noteq> zero_r \<Longrightarrow> degree (monomial Nat_O c) = Nat_O"
  and deg_constant  : "\<And>p.     (degree p = Nat_O) \<longleftrightarrow> (\<exists>c. p = monomial Nat_O c)"
  and deg_X_minus_ax : "\<And>a.    degree (monomial (Nat_S Nat_O) one_r +P monomial Nat_O (opp_r a)) = Nat_S Nat_O"
  and deg_mul       : "\<And>p q.   p \<noteq> zero_p \<Longrightarrow> q \<noteq> zero_p \<Longrightarrow>
                                 degree (p *P q) = mynat_add (degree p) (degree q)"
  and C_zero_ax     : "monomial Nat_O zero_r = zero_p"
  and C_one_ax      : "monomial Nat_O one_r = one_p"
  and euclid_X_minus_ax :
       "\<And>p a. \<exists>q r.
          p = q *P (monomial (Nat_S Nat_O) one_r +P monomial Nat_O (opp_r a)) +P r
          \<and> degree r = Nat_O"
begin





definition X :: "'p" where
  "X = monomial (Nat_S Nat_O) one_r"

definition C :: "'r \<Rightarrow> 'p" where
  "C c = monomial Nat_O c"

definition X_minus :: "'r \<Rightarrow> 'p" where
  "X_minus a = X +P C (opp_r a)"

fun poly_of_roots :: "'r mylist \<Rightarrow> 'p" where
  "poly_of_roots NilL = one_p"
| "poly_of_roots (ConsL a xs) = X_minus a *P poly_of_roots xs"

definition is_root :: "'r \<Rightarrow> 'p \<Rightarrow> bool" where
  "is_root a p \<longleftrightarrow> eval p a = zero_r"





lemma X_minus_unfold:
  "X_minus a = monomial (Nat_S Nat_O) one_r +P monomial Nat_O (opp_r a)"
  unfolding X_minus_def X_def C_def
  sorry
lemma eval_C: "eval (C c) x = c"
  unfolding C_def
  sorry
lemma eval_X: "eval X x = x"
  unfolding X_def
  sorry
lemma deg_X_minus: "degree (X_minus a) = Nat_S Nat_O"
  sorry
lemma C_zero: "C zero_r = zero_p"
  unfolding C_def
  sorry
lemma C_one: "C one_r = one_p"
  unfolding C_def
  sorry
lemma deg_C: "c \<noteq> zero_r \<Longrightarrow> degree (C c) = Nat_O"
  unfolding C_def
  sorry
lemma euclid_X_minus: "\<exists>q r. p = q *P X_minus a +P r \<and> degree r = Nat_O"
  using euclid_X_minus_ax[of p a]
  sorry




lemma r_opp_add: "opp_r x +R x = zero_r"
  sorry
lemma r_add_zero_l: "zero_r +R x = x"
  sorry




lemma sub_eq_zero_l: "x +R opp_r y = zero_r \<Longrightarrow> x = y"
  sorry




lemma eval_X_minus: "eval (X_minus a) b = b +R opp_r a"
  unfolding X_minus_def
  sorry




lemma X_minus_nonzero: "X_minus a \<noteq> zero_p"
  sorry




lemma p_add_zero_l: "zero_p +P x = x"
  sorry
lemma p_mul_zero_l: "zero_p *P x = zero_p"
  sorry
lemma p_mul_one_l: "one_p *P x = x"
  sorry




lemma root_factor: "is_root a p \<Longrightarrow> \<exists>q. p = q *P X_minus a"
  sorry




lemma root_transfer:
  "p = q *P X_minus a \<Longrightarrow> b \<noteq> a \<Longrightarrow> is_root b p \<Longrightarrow> is_root b q"
  sorry




lemma roots_le_degree:
  "NoDupL xs \<Longrightarrow> (\<forall>a. InL a xs \<longrightarrow> is_root a p) \<Longrightarrow> p \<noteq> zero_p \<Longrightarrow>
   mynat_le (lengthL xs) (degree p)"
  sorry




lemma constant_root_zero:
  "degree p = Nat_O \<Longrightarrow> is_root a p \<Longrightarrow> p = zero_p"
  sorry




lemma root_of_product:
  "is_root a (p *P q) \<Longrightarrow> is_root a p \<or> is_root a q"
  sorry




lemma root_scale_constant:
  "c \<noteq> zero_r \<Longrightarrow> (is_root a p \<longleftrightarrow> is_root a (C c *P p))"
  sorry




lemma poly_of_roots_nonzero: "poly_of_roots xs \<noteq> zero_p"
  sorry




lemma deg_poly_of_roots: "degree (poly_of_roots xs) = lengthL xs"
  sorry




lemma root_factor_list:
  "NoDupL xs \<Longrightarrow> (\<forall>a. InL a xs \<longrightarrow> is_root a p) \<Longrightarrow>
   \<exists>q. p = q *P poly_of_roots xs"
  sorry




lemma degree_factorisation:
  "p = q *P poly_of_roots xs \<Longrightarrow> q \<noteq> zero_p \<Longrightarrow>
   degree p = mynat_add (degree q) (lengthL xs)"
  sorry
end

end
