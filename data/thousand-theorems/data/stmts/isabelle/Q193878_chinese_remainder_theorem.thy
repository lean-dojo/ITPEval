(*
  Statement-only formalization of thousand-theorems corpus artifact Q193878
  (thousand-theorems__isabelle__Q193878), "Chinese remainder theorem":
  pairwise coprime ideals indexed by a finite carrier in a commutative ring
  yield a canonical ring isomorphism from the quotient by their intersection
  to the product of the individual quotient rings. This file contains no proof.
*)

theory Q193878_chinese_remainder_theorem
  imports "HOL-Algebra.Chinese_Remainder"
begin

definition q193878_ideal_intersection ::
    "('a, 'b) ring_scheme \<Rightarrow> 'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where
    "q193878_ideal_intersection R K I =
      {x \<in> carrier R. \<forall>i \<in> K. x \<in> I i}"

definition q193878_quotient_product ::
    "('a, 'b) ring_scheme \<Rightarrow> 'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow>
      ('i \<Rightarrow> 'a set) ring"
  where
    "q193878_quotient_product R K I =
      \<lparr>carrier = PiE K (\<lambda>i. carrier (R Quot I i)),
       mult = (\<lambda>f g. restrict
         (\<lambda>i. f i \<otimes>\<^bsub>R Quot I i\<^esub> g i) K),
       one = restrict (\<lambda>i. \<one>\<^bsub>R Quot I i\<^esub>) K,
       zero = restrict (\<lambda>i. \<zero>\<^bsub>R Quot I i\<^esub>) K,
       add = (\<lambda>f g. restrict
         (\<lambda>i. f i \<oplus>\<^bsub>R Quot I i\<^esub> g i) K)\<rparr>"

theorem chinese_remainder_theorem:
  fixes R :: "('a, 'b) ring_scheme"
    and K :: "'i set"
    and I :: "'i \<Rightarrow> 'a set"
  assumes "cring R"
    and "finite K"
    and "\<And>i. i \<in> K \<Longrightarrow> ideal (I i) R"
    and "\<And>i j. i \<in> K \<Longrightarrow> j \<in> K \<Longrightarrow> i \<noteq> j \<Longrightarrow>
      I i <+>\<^bsub>R\<^esub> I j = carrier R"
  shows "\<exists>h. h \<in> ring_iso
      (R Quot (q193878_ideal_intersection R K I))
      (q193878_quotient_product R K I) \<and>
    (\<forall>a \<in> carrier R.
      h (q193878_ideal_intersection R K I +>\<^bsub>R\<^esub> a) =
        restrict (\<lambda>i. I i +>\<^bsub>R\<^esub> a) K)"
  oops

end
