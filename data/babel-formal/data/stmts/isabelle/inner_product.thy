theory inner_product
  imports Main
begin

locale inner_product =
  fixes zero_R one_R :: "'r"
    and add_R :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl "+R" 65)
    and mul_R :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl "*R" 70)
    and opp_R :: "'r \<Rightarrow> 'r"
    and zeroV :: "'v"
    and addV  :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"  (infixl "+V" 65)
    and oppV  :: "'v \<Rightarrow> 'v"
    and smul  :: "'r \<Rightarrow> 'v \<Rightarrow> 'v"
    and ip    :: "'v \<Rightarrow> 'v \<Rightarrow> 'r"

  assumes add_R_comm    : "\<And>x y. x +R y = y +R x"
    and   add_R_assoc   : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and   add_R_zero    : "\<And>x. x +R zero_R = x"
    and   zero_R_add    : "\<And>x. zero_R +R x = x"
    and   add_R_opp     : "\<And>x. x +R opp_R x = zero_R"
    and   mul_R_comm    : "\<And>x y. x *R y = y *R x"
    and   mul_R_assoc   : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
    and   mul_R_one     : "\<And>x. x *R one_R = x"
    and   mul_opp_one   : "\<And>x. opp_R one_R *R x = opp_R x"
    and   opp_R_opp     : "\<And>x. opp_R (opp_R x) = x"

    and   addV_comm     : "\<And>u v. u +V v = v +V u"
    and   addV_assoc    : "\<And>u v w. (u +V v) +V w = u +V (v +V w)"
    and   addV_zero     : "\<And>u. u +V zeroV = u"
    and   smul_addV     : "\<And>a u v. smul a (u +V v) = smul a u +V smul a v"
    and   one_smul      : "\<And>u. smul one_R u = u"
    and   opp_smul_one  : "\<And>u. oppV u = smul (opp_R one_R) u"

    and   lin_left_add  : "\<And>u v w. ip (u +V v) w = ip u w +R ip v w"
    and   lin_left_smul : "\<And>a u v. ip (smul a u) v = a *R ip u v"
    and   lin_right_add : "\<And>u v w. ip u (v +V w) = ip u v +R ip u w"
    and   lin_right_smul: "\<And>a u v. ip u (smul a v) = a *R ip u v"
    and   ip_symm       : "\<And>u v. ip u v = ip v u"
begin





definition subV :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"  (infixl "-V" 65)
  where "u -V v \<equiv> u +V oppV v"

lemma add_R_left_comm: "x +R (y +R z) = y +R (x +R z)"
  sorry




lemma ip_neg_left: "ip (oppV u) v = opp_R (ip u v)"
  sorry
lemma ip_neg_right: "ip u (oppV v) = opp_R (ip u v)"
  sorry




lemma ip_add_add:
  "ip (u +V v) (u +V v) =
    (ip u u +R ip v u) +R (ip u v +R ip v v)"
  sorry




lemma ip_neg_neg: "ip (oppV v) (oppV v) = ip v v"
  sorry
lemma ip_sub_sub:
  "ip (u -V v) (u -V v) =
    (ip u u +R opp_R (ip v u)) +R (opp_R (ip u v) +R ip v v)"
  sorry




lemma pythagoras:
  assumes h: "ip u v = zero_R"
  shows "ip (u +V v) (u +V v) = ip u u +R ip v v"
  sorry




lemma parallelogram:
  "ip (u +V v) (u +V v) +R ip (u -V v) (u -V v) =
    ((ip u u +R ip v u) +R (ip u v +R ip v v)) +R
    ((ip u u +R opp_R (ip v u)) +R (opp_R (ip u v) +R ip v v))"
  sorry
end

end
