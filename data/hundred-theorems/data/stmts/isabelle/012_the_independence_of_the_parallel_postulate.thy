(*
  Statement-only formalization of the independence of the parallel postulate
  from Hundred Theorems item 012. The Klein disc satisfies Tarski's axioms
  1-9 and 11 while refuting the Euclidean axiom 10. This file contains no
  proof.
*)

theory Independence_Of_The_Parallel_Postulate
  imports Complex_Main
begin

type_synonym point2 = "real \<times> real"

definition dot2 :: "point2 \<Rightarrow> point2 \<Rightarrow> real"
  where
    "dot2 u v = fst u * fst v + snd u * snd v"

definition norm_sq2 :: "point2 \<Rightarrow> real"
  where
    "norm_sq2 u = dot2 u u"

definition klein_disc :: "point2 set"
  where
    "klein_disc = {u. norm_sq2 u < 1}"

definition affine_combination ::
    "real \<Rightarrow> point2 \<Rightarrow> point2 \<Rightarrow> point2"
  where
    "affine_combination t u v =
      ((1 - t) * fst u + t * fst v,
       (1 - t) * snd u + t * snd v)"

definition klein_between ::
    "point2 \<Rightarrow> point2 \<Rightarrow> point2 \<Rightarrow> bool"
  where
    "klein_between y x z \<longleftrightarrow>
      y \<in> klein_disc \<and> x \<in> klein_disc \<and> z \<in> klein_disc \<and>
      (\<exists>t. 0 \<le> t \<and> t \<le> 1 \<and> y = affine_combination t x z)"

definition klein_ddist :: "point2 \<Rightarrow> point2 \<Rightarrow> real"
  where
    "klein_ddist u v =
      (1 - dot2 u v) ^ 2
        / ((1 - norm_sq2 u) * (1 - norm_sq2 v)) - 1"

definition klein_congruent ::
    "point2 \<Rightarrow> point2 \<Rightarrow> point2 \<Rightarrow> point2 \<Rightarrow> bool"
  where
    "klein_congruent a b c d \<longleftrightarrow>
      klein_ddist a b = klein_ddist c d"

definition tarski_axiom_1 :: bool
  where
    "tarski_axiom_1 \<longleftrightarrow>
      (\<forall>a\<in>klein_disc. \<forall>b\<in>klein_disc.
        klein_congruent a b b a)"

definition tarski_axiom_2 :: bool
  where
    "tarski_axiom_2 \<longleftrightarrow>
      (\<forall>a\<in>klein_disc. \<forall>b\<in>klein_disc.
       \<forall>p\<in>klein_disc. \<forall>q\<in>klein_disc.
       \<forall>r\<in>klein_disc. \<forall>s\<in>klein_disc.
        klein_congruent a b p q \<and> klein_congruent a b r s
          \<longrightarrow> klein_congruent p q r s)"

definition tarski_axiom_3 :: bool
  where
    "tarski_axiom_3 \<longleftrightarrow>
      (\<forall>a\<in>klein_disc. \<forall>b\<in>klein_disc. \<forall>c\<in>klein_disc.
        klein_congruent a b c c \<longrightarrow> a = b)"

definition tarski_axiom_4 :: bool
  where
    "tarski_axiom_4 \<longleftrightarrow>
      (\<forall>q\<in>klein_disc. \<forall>a\<in>klein_disc.
       \<forall>b\<in>klein_disc. \<forall>c\<in>klein_disc.
        \<exists>x\<in>klein_disc.
          klein_between a q x \<and> klein_congruent a x b c)"

definition tarski_axiom_5 :: bool
  where
    "tarski_axiom_5 \<longleftrightarrow>
      (\<forall>a\<in>klein_disc. \<forall>b\<in>klein_disc.
       \<forall>c\<in>klein_disc. \<forall>x\<in>klein_disc.
       \<forall>a'\<in>klein_disc. \<forall>b'\<in>klein_disc.
       \<forall>c'\<in>klein_disc. \<forall>x'\<in>klein_disc.
        a \<noteq> b \<and>
        klein_congruent a b a' b' \<and>
        klein_congruent a c a' c' \<and>
        klein_congruent b c b' c' \<and>
        klein_between b a x \<and>
        klein_between b' a' x' \<and>
        klein_congruent b x b' x'
          \<longrightarrow> klein_congruent c x c' x')"

definition tarski_axiom_6 :: bool
  where
    "tarski_axiom_6 \<longleftrightarrow>
      (\<forall>a\<in>klein_disc. \<forall>b\<in>klein_disc.
        klein_between b a a \<longrightarrow> a = b)"

definition tarski_axiom_7 :: bool
  where
    "tarski_axiom_7 \<longleftrightarrow>
      (\<forall>a\<in>klein_disc. \<forall>b\<in>klein_disc.
       \<forall>c\<in>klein_disc. \<forall>p\<in>klein_disc. \<forall>q\<in>klein_disc.
        klein_between p a c \<and> klein_between q b c
          \<longrightarrow> (\<exists>x\<in>klein_disc.
            klein_between x p b \<and> klein_between x q a))"

definition tarski_axiom_8 :: bool
  where
    "tarski_axiom_8 \<longleftrightarrow>
      (\<exists>a\<in>klein_disc. \<exists>b\<in>klein_disc. \<exists>c\<in>klein_disc.
        \<not> klein_between b a c \<and>
        \<not> klein_between c b a \<and>
        \<not> klein_between a c b)"

definition tarski_axiom_9 :: bool
  where
    "tarski_axiom_9 \<longleftrightarrow>
      (\<forall>p\<in>klein_disc. \<forall>q\<in>klein_disc.
       \<forall>a\<in>klein_disc. \<forall>b\<in>klein_disc. \<forall>c\<in>klein_disc.
        p \<noteq> q \<and>
        klein_congruent a p a q \<and>
        klein_congruent b p b q \<and>
        klein_congruent c p c q
          \<longrightarrow>
            klein_between b a c \<or>
            klein_between c b a \<or>
            klein_between a c b)"

definition tarski_axiom_10 :: bool
  where
    "tarski_axiom_10 \<longleftrightarrow>
      (\<forall>a\<in>klein_disc. \<forall>b\<in>klein_disc.
       \<forall>c\<in>klein_disc. \<forall>d\<in>klein_disc. \<forall>t\<in>klein_disc.
        klein_between d a t \<and> klein_between d b c \<and> a \<noteq> d
          \<longrightarrow> (\<exists>x\<in>klein_disc. \<exists>y\<in>klein_disc.
            klein_between b a x \<and>
            klein_between c a y \<and>
            klein_between t x y))"

definition tarski_axiom_11 :: bool
  where
    "tarski_axiom_11 \<longleftrightarrow>
      (\<forall>X Y :: point2 set.
        X \<subseteq> klein_disc \<and> Y \<subseteq> klein_disc \<and>
        (\<exists>a\<in>klein_disc.
          \<forall>x\<in>X. \<forall>y\<in>Y. klein_between x a y)
          \<longrightarrow> (\<exists>b\<in>klein_disc.
            \<forall>x\<in>X. \<forall>y\<in>Y. klein_between b x y))"

theorem klein_disc_independence_of_parallel_postulate:
  "tarski_axiom_1 \<and>
   tarski_axiom_2 \<and>
   tarski_axiom_3 \<and>
   tarski_axiom_4 \<and>
   tarski_axiom_5 \<and>
   tarski_axiom_6 \<and>
   tarski_axiom_7 \<and>
   tarski_axiom_8 \<and>
   tarski_axiom_9 \<and>
   \<not> tarski_axiom_10 \<and>
   tarski_axiom_11"
  sorry

end
