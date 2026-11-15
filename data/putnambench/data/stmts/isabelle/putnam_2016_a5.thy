theory putnam_2016_a5 imports Complex_Main
"HOL-Algebra.Multiplicative_Group"
begin

theorem putnam_2016_a5:
  fixes G (structure) and g h :: "'a" and S :: "'a set"
  defines "S \<equiv> {
    g \<otimes>\<^bsub>G\<^esub> h,
    inv\<^bsub>G\<^esub> g \<otimes>\<^bsub>G\<^esub> h,
    g \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> h,
    inv\<^bsub>G\<^esub> g \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> h}"
  assumes hG : "Group.group G \<and> finite (carrier G)"
    and ghmem : "g \<in> carrier G \<and> h \<in> carrier G"
    and ghgen : "generate G {h, g} = carrier G"
    and godd : "odd (group.ord G g)"
  shows "\<forall>x \<in> carrier G. \<exists>mn :: 'a list.
    1 \<le> length mn \<and>
    length mn \<le> card (carrier G) \<and>
    set mn \<subseteq> S \<and>
    foldr (\<otimes>\<^bsub>G\<^esub>) mn \<one>\<^bsub>G\<^esub> = x"
  sorry

end
