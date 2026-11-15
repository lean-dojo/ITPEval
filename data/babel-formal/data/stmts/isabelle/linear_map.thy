theory linear_map
  imports Main
begin





locale linear_map_setup =
  fixes zeroV :: "'v"
    and addV  :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"         (infixl "+V" 65)
    and smul  :: "'r \<Rightarrow> 'v \<Rightarrow> 'v"           (infixr "\<cdot>V" 70)
    and zeroW :: "'w"
    and addW  :: "'w \<Rightarrow> 'w \<Rightarrow> 'w"         (infixl "+W" 65)
    and smulW :: "'r \<Rightarrow> 'w \<Rightarrow> 'w"           (infixr "\<cdot>W" 70)
    and toFun :: "'v \<Rightarrow> 'w"

  assumes addV_comm  : "\<And>u v. u +V v = v +V u"
    and   addV_assoc : "\<And>u v w. (u +V v) +V w = u +V (v +V w)"
    and   addV_zero  : "\<And>u. u +V zeroV = u"
    and   smul_zeroV : "\<And>a. a \<cdot>V zeroV = zeroV"

    and   addW_comm  : "\<And>u v. u +W v = v +W u"
    and   addW_assoc : "\<And>u v w. (u +W v) +W w = u +W (v +W w)"
    and   addW_zero  : "\<And>u. u +W zeroW = u"
    and   smulW_zero : "\<And>a. a \<cdot>W zeroW = zeroW"

    and   map_add    : "\<And>u v. toFun (u +V v) = toFun u +W toFun v"
    and   map_smul   : "\<And>a u. toFun (a \<cdot>V u) = a \<cdot>W toFun u"
begin





definition ker :: "'v \<Rightarrow> bool"
  where "ker x \<equiv> toFun x = zeroW"

definition im :: "'w \<Rightarrow> bool"
  where "im y \<equiv> \<exists>x. toFun x = y"





lemma ker_add:
  assumes "ker x" "ker y" shows "ker (x +V y)"
  sorry
lemma ker_smul:
  assumes "ker x" shows "ker (a \<cdot>V x)"
  sorry




lemma im_add:
  assumes "im y" "im z" shows "im (y +W z)"
  sorry
lemma im_smul:
  assumes "im y" shows "im (a \<cdot>W y)"
  sorry
end

end
