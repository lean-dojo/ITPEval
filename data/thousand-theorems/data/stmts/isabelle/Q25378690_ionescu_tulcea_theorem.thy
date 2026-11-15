(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q25378690, "Ionescu-Tulcea theorem": a sequence of Markov kernels depending
  measurably on each finite history determines a Markov kernel from every
  initial history to infinite trajectories, with the prescribed iterated
  finite-dimensional marginals. This file contains no proof.
*)

theory Q25378690_ionescu_tulcea_theorem
  imports "HOL.Complex_Main"
begin

type_synonym 'a q25378690_measurable_space = "'a set \<times> 'a set set"
type_synonym 'a q25378690_probability = "'a set \<Rightarrow> real"

definition q25378690_space ::
    "'a q25378690_measurable_space \<Rightarrow> 'a set" where
  "q25378690_space M = fst M"

definition q25378690_sets ::
    "'a q25378690_measurable_space \<Rightarrow> 'a set set" where
  "q25378690_sets M = snd M"

definition q25378690_sigma_field ::
    "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "q25378690_sigma_field \<Omega> A \<longleftrightarrow>
    A \<subseteq> Pow \<Omega> \<and>
    {} \<in> A \<and>
    (\<forall>E \<in> A. \<Omega> - E \<in> A) \<and>
    (\<forall>E :: nat \<Rightarrow> 'a set.
      (\<forall>n. E n \<in> A) \<longrightarrow> (\<Union>n. E n) \<in> A)"

definition q25378690_measurable_space ::
    "'a q25378690_measurable_space \<Rightarrow> bool" where
  "q25378690_measurable_space M \<longleftrightarrow>
    q25378690_sigma_field (q25378690_space M) (q25378690_sets M)"

definition q25378690_generated ::
    "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
  "q25378690_generated \<Omega> G =
    \<Inter>{A. q25378690_sigma_field \<Omega> A \<and> G \<subseteq> A}"

definition q25378690_pie ::
    "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a) set" where
  "q25378690_pie I F =
    {x. (\<forall>i \<in> I. x i \<in> F i) \<and>
      (\<forall>i. i \<notin> I \<longrightarrow> x i = undefined)}"

definition q25378690_restrict ::
    "('i \<Rightarrow> 'a) \<Rightarrow> 'i set \<Rightarrow> ('i \<Rightarrow> 'a)" where
  "q25378690_restrict x I =
    (\<lambda>i. if i \<in> I then x i else undefined)"

definition q25378690_update ::
    "('i \<Rightarrow> 'a) \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> ('i \<Rightarrow> 'a)" where
  "q25378690_update x i y =
    (\<lambda>j. if j = i then y else x j)"

definition q25378690_cylinders ::
    "'i set \<Rightarrow> ('i \<Rightarrow> 'a q25378690_measurable_space) \<Rightarrow>
     ('i \<Rightarrow> 'a) set set" where
  "q25378690_cylinders I M =
    {C. \<exists>i \<in> I. \<exists>E \<in> q25378690_sets (M i).
      C = {x \<in> q25378690_pie I
        (\<lambda>j. q25378690_space (M j)). x i \<in> E}}"

definition q25378690_product_space ::
    "'i set \<Rightarrow> ('i \<Rightarrow> 'a q25378690_measurable_space) \<Rightarrow>
     ('i \<Rightarrow> 'a) q25378690_measurable_space" where
  "q25378690_product_space I M =
    (q25378690_pie I (\<lambda>i. q25378690_space (M i)),
     q25378690_generated
       (q25378690_pie I (\<lambda>i. q25378690_space (M i)))
       (q25378690_cylinders I M))"

definition q25378690_probability_measure ::
    "'a q25378690_measurable_space \<Rightarrow>
     'a q25378690_probability \<Rightarrow> bool" where
  "q25378690_probability_measure M \<mu> \<longleftrightarrow>
    q25378690_measurable_space M \<and>
    (\<forall>E. \<mu> E = \<mu> (E \<inter> q25378690_space M)) \<and>
    \<mu> {} = 0 \<and>
    \<mu> (q25378690_space M) = 1 \<and>
    (\<forall>E \<in> q25378690_sets M. 0 \<le> \<mu> E \<and> \<mu> E \<le> 1) \<and>
    (\<forall>E :: nat \<Rightarrow> 'a set.
      (\<forall>n. E n \<in> q25378690_sets M) \<and>
      (\<forall>i j. i \<noteq> j \<longrightarrow> E i \<inter> E j = {})
      \<longrightarrow>
      \<mu> (\<Union>n. E n) =
        Sup (range (\<lambda>n. sum (\<lambda>i. \<mu> (E i)) {0..<n})))"

definition q25378690_markov_kernel ::
    "'a q25378690_measurable_space \<Rightarrow>
     'b q25378690_measurable_space \<Rightarrow>
     ('a \<Rightarrow> 'b q25378690_probability) \<Rightarrow> bool" where
  "q25378690_markov_kernel A B K \<longleftrightarrow>
    q25378690_measurable_space A \<and>
    q25378690_measurable_space B \<and>
    (\<forall>x \<in> q25378690_space A.
      q25378690_probability_measure B (K x)) \<and>
    (\<forall>E \<in> q25378690_sets B. \<forall>r :: real.
      {x \<in> q25378690_space A. r < K x E} \<in> q25378690_sets A)"

definition q25378690_nn_integral ::
    "'a q25378690_measurable_space \<Rightarrow>
     'a q25378690_probability \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
  "q25378690_nn_integral M \<mu> f =
    Sup {sum
      (\<lambda>r. r * \<mu> {x \<in> q25378690_space M. g x = r})
      (g ` q25378690_space M) |g.
      finite (g ` q25378690_space M) \<and>
      (\<forall>x \<in> q25378690_space M. 0 \<le> g x \<and> g x \<le> f x) \<and>
      (\<forall>r. {x \<in> q25378690_space M. g x = r}
        \<in> q25378690_sets M)}"

definition q25378690_return ::
    "'a \<Rightarrow> 'a q25378690_probability" where
  "q25378690_return x E = (if x \<in> E then 1 else 0)"

definition q25378690_bind ::
    "'a q25378690_measurable_space \<Rightarrow>
     'a q25378690_probability \<Rightarrow>
     ('a \<Rightarrow> 'b q25378690_probability) \<Rightarrow>
     'b q25378690_probability" where
  "q25378690_bind M \<mu> K E =
    q25378690_nn_integral M \<mu> (\<lambda>x. K x E)"

definition q25378690_extend ::
    "(nat \<Rightarrow> 'a q25378690_measurable_space) \<Rightarrow>
     (nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
       'a q25378690_probability) \<Rightarrow>
     nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
     (nat \<Rightarrow> 'a) q25378690_probability" where
  "q25378690_extend M \<kappa> n \<omega> E =
    \<kappa> n \<omega>
      {y \<in> q25378690_space (M (Suc n)).
        q25378690_update \<omega> (Suc n) y \<in> E}"

primrec q25378690_partial ::
    "(nat \<Rightarrow> 'a q25378690_measurable_space) \<Rightarrow>
     (nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
       'a q25378690_probability) \<Rightarrow>
     nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
     (nat \<Rightarrow> 'a) q25378690_probability" where
  "q25378690_partial M \<kappa> a 0 \<omega> =
    q25378690_return \<omega>"
| "q25378690_partial M \<kappa> a (Suc m) \<omega> =
    q25378690_bind
      (q25378690_product_space {0..<Suc a + m} M)
      (q25378690_partial M \<kappa> a m \<omega>)
      (q25378690_extend M \<kappa> (a + m))"

definition q25378690_ionescu_tulcea ::
    "(nat \<Rightarrow> 'a q25378690_measurable_space) \<Rightarrow>
     (nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
       'a q25378690_probability) \<Rightarrow> bool" where
  "q25378690_ionescu_tulcea M \<kappa> \<longleftrightarrow>
    ((\<forall>n. q25378690_measurable_space (M n)) \<and>
     (\<forall>n. q25378690_markov_kernel
      (q25378690_product_space {0..<Suc n} M)
      (M (Suc n)) (\<kappa> n)))
    \<longrightarrow>
    (\<exists>traj ::
      nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
        (nat \<Rightarrow> 'a) q25378690_probability.
      (\<forall>a. q25378690_markov_kernel
        (q25378690_product_space {0..<Suc a} M)
        (q25378690_product_space UNIV M) (traj a)) \<and>
      (\<forall>a m \<omega> E.
        \<omega> \<in> q25378690_space
          (q25378690_product_space {0..<Suc a} M) \<and>
        E \<in> q25378690_sets
          (q25378690_product_space {0..<Suc a + m} M)
        \<longrightarrow>
        traj a \<omega>
          {x \<in> q25378690_space (q25378690_product_space UNIV M).
            q25378690_restrict x {0..<Suc a + m} \<in> E} =
        q25378690_partial M \<kappa> a m \<omega> E))"

end
