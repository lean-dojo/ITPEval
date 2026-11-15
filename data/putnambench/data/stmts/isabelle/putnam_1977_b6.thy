theory putnam_1977_b6 imports Complex_Main
"HOL-Algebra.Group"
begin

theorem putnam_1977_b6:
  fixes G (structure)
    and h :: "nat"
    and a :: "'a"
    and P H :: "'a set"
  defines "P \<equiv> {g :: 'a. \<exists> x :: 'a list.
    x \<noteq> [] \<and> set x \<subseteq> H \<and>
    g = foldr (\<lambda> y z. (y \<otimes>\<^bsub>G\<^esub> a) \<otimes>\<^bsub>G\<^esub> z) x \<one>\<^bsub>G\<^esub>}"
  assumes hG : "Group.group G"
    and ha : "a \<in> carrier G"
    and hH : "finite H \<and> subgroup H G"
    and hh : "h = card H"
    and haH : "\<forall> x \<in> H. (x \<otimes>\<^bsub>G\<^esub> a)[^]3 = \<one>\<^bsub>G\<^esub>"
  shows "finite P \<and> card P \<le> 3 * h^2"
  sorry

end
