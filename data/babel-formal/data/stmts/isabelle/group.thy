theory group
  imports Main
begin



locale group =
  fixes mul :: "'a => 'a => 'a"  (infixl "**" 70)
    and one :: "'a"
    and inv :: "'a => 'a"
  assumes mul_assoc : "a ** (b ** c) = (a ** b) ** c"
    and   mul_one   : "a ** one = a"
    and   one_mul   : "one ** a = a"
    and   mul_inv_l : "inv a ** a = one"
    and   mul_inv_r : "a ** inv a = one"
begin



lemma mul_left_cancel:
  assumes h: "a ** b = a ** c"
  shows "b = c"
  sorry
lemma mul_right_cancel:
  assumes h: "b ** a = c ** a"
  shows "b = c"
  sorry
lemma inv_inv: "inv (inv a) = a"
  sorry
lemma inv_mul: "inv (a ** b) = inv b ** inv a"
  sorry
lemma inv_eq_of_mul_eq_one:
  assumes h: "a ** b = one"
  shows "b = inv a"
  sorry
end




locale group_comm = group +
  assumes mul_comm : "a ** b = b ** a"
begin

lemma mul_rotate': "a ** (b ** c) = b ** (c ** a)"
  sorry
end




locale group_action =
  group mul one inv
    for mul :: "'a => 'a => 'a"  (infixl "**" 70)
    and one :: "'a"
    and inv :: "'a => 'a" +
  fixes act :: "'a => 'b => 'b"  (infixr "acts" 73)
  assumes act_one : "one acts x = x"
    and   act_mul : "(g ** h) acts x = g acts (h acts x)"
begin



lemma act_inv: "inv g acts (g acts x) = x"
  sorry
lemma act_inv_r: "g acts (inv g acts x) = x"
  sorry
definition orbit :: "'b => 'b => bool"
  where "orbit x y == (EX g. g acts x = y)"

definition stabilizer :: "'b => 'a => bool"
  where "stabilizer x g == g acts x = x"

lemma orbit_refl: "orbit x x"
  sorry
lemma orbit_sym:
  assumes "orbit x y"
  shows "orbit y x"
  sorry
lemma orbit_trans:
  assumes "orbit x y" "orbit y z"
  shows "orbit x z"
  sorry
lemma orbit_partition:
  assumes hxy: "orbit x y"
  shows "orbit x z = orbit y z"
  sorry
lemma stabilizer_mul:
  assumes "stabilizer x g" "stabilizer x h"
  shows "stabilizer x (g ** h)"
  sorry
lemma stabilizer_inv:
  assumes hg: "stabilizer x g"
  shows "stabilizer x (inv g)"
  sorry
lemma stabilizer_one: "stabilizer x one"
  sorry
lemma stabilizer_conjugate:
  assumes hh: "stabilizer x h"
  shows "stabilizer (g acts x) (g ** h ** inv g)"
  sorry
lemma stabilizer_conjugate_orbit:
  assumes hxy: "g acts x = y"
  shows "stabilizer y h = stabilizer x (inv g ** h ** g)"
  sorry
end

end
