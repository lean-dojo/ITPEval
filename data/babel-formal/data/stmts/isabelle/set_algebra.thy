theory set_algebra
  imports Main
begin

definition sUnion :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
  where "sUnion A B \<equiv> \<lambda>x. A x \<or> B x"

definition sInter :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
  where "sInter A B \<equiv> \<lambda>x. A x \<and> B x"

definition sCompl :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
  where "sCompl A \<equiv> \<lambda>x. \<not> A x"

lemma inter_distrib_left:
  "\<forall>x. sInter A (sUnion B C) x \<longleftrightarrow> sUnion (sInter A B) (sInter A C) x"
  sorry
lemma inter_distrib_right:
  "\<forall>x. sInter (sUnion A B) C x \<longleftrightarrow> sUnion (sInter A C) (sInter B C) x"
  sorry
lemma de_morgan_union:
  "\<forall>x. sCompl (sUnion A B) x \<longleftrightarrow> sInter (sCompl A) (sCompl B) x"
  sorry
lemma de_morgan_inter:
  "\<forall>x. sCompl (sInter A B) x \<longleftrightarrow> sUnion (sCompl A) (sCompl B) x"
  sorry
end
