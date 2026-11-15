theory ideals
  imports Main
begin

locale cring =
  fixes zero :: "'r"
    and one  :: "'r"
    and add  :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl "+R" 65)
    and mul  :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl "*R" 70)
    and opp  :: "'r \<Rightarrow> 'r"
  assumes add_comm  : "\<And>x y. x +R y = y +R x"
    and   add_assoc : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and   add_zero  : "\<And>x. x +R zero = x"
    and   add_opp   : "\<And>x. x +R opp x = zero"
    and   mul_comm  : "\<And>x y. x *R y = y *R x"
    and   mul_assoc : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
    and   mul_one   : "\<And>x. x *R one = x"
    and   dist_l    : "\<And>a x y. a *R (x +R y) = (a *R x) +R (a *R y)"
    and   opp_add   : "\<And>x y. opp (x +R y) = opp x +R opp y"
begin


lemma add_left_comm: "x +R (y +R z) = y +R (x +R z)"
  sorry
lemma zero_add: "zero +R x = x"
  sorry




definition IsIdeal :: "('r \<Rightarrow> bool) \<Rightarrow> bool"
  where "IsIdeal I \<equiv>
    I zero \<and>
    (\<forall>x y. I x \<longrightarrow> I y \<longrightarrow> I (x +R y)) \<and>
    (\<forall>x.   I x \<longrightarrow> I (opp x)) \<and>
    (\<forall>a x. I x \<longrightarrow> I (a *R x))"





definition Inter :: "('i \<Rightarrow> 'r \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool"
  where "Inter F \<equiv> \<lambda>x. \<forall>i. F i x"

lemma inter_isIdeal:
  assumes h: "\<forall>i. IsIdeal (F i)"
  shows "IsIdeal (Inter F)"
  sorry




definition isum :: "('r \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool"
  where "isum I J \<equiv> \<lambda>x. \<exists>a b. I a \<and> J b \<and> x = a +R b"

lemma sum_isIdeal:
  assumes hI: "IsIdeal I" and hJ: "IsIdeal J"
  shows "IsIdeal (isum I J)"
  sorry
end

end
