(*
  Statement-only formalization of thousand-theorems corpus artifact Q1816952
  (thousand-theorems__isabelle__Q1816952), "Schur's lemma": over an
  algebraically closed field, the finite-dimensional endomorphism space of a
  simple object in a linear preadditive category with kernels is
  one-dimensional. This file contains no proof.
*)

theory Q1816952_schur_s_lemma
  imports Main
begin

record ('o, 'm, 'k) q1816952_linear_category_data =
  objects :: "'o set"
  arrows :: "'m set"
  source :: "'m \<Rightarrow> 'o"
  target :: "'m \<Rightarrow> 'o"
  identity :: "'o \<Rightarrow> 'm"
  compose :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"
  zero_arrow :: "'o \<Rightarrow> 'o \<Rightarrow> 'm"
  add_arrow :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"
  neg_arrow :: "'m \<Rightarrow> 'm"
  scalar_arrow :: "'k \<Rightarrow> 'm \<Rightarrow> 'm"

definition q1816952_hom ::
    "('o, 'm, 'k) q1816952_linear_category_data \<Rightarrow>
      'o \<Rightarrow> 'o \<Rightarrow> 'm set" where
  "q1816952_hom C X Y =
    {f \<in> arrows C. source C f = X \<and> target C f = Y}"

definition q1816952_is_category ::
    "('o, 'm, 'k) q1816952_linear_category_data \<Rightarrow> bool" where
  "q1816952_is_category C \<longleftrightarrow>
    (\<forall>f \<in> arrows C.
      source C f \<in> objects C \<and> target C f \<in> objects C) \<and>
    (\<forall>X \<in> objects C.
      identity C X \<in> q1816952_hom C X X) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C. \<forall>Z \<in> objects C.
      \<forall>f \<in> q1816952_hom C X Y. \<forall>g \<in> q1816952_hom C Y Z.
        compose C g f \<in> q1816952_hom C X Z) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      \<forall>f \<in> q1816952_hom C X Y.
        compose C (identity C Y) f = f \<and>
        compose C f (identity C X) = f) \<and>
    (\<forall>W \<in> objects C. \<forall>X \<in> objects C.
      \<forall>Y \<in> objects C. \<forall>Z \<in> objects C.
      \<forall>f \<in> q1816952_hom C W X.
      \<forall>g \<in> q1816952_hom C X Y.
      \<forall>h \<in> q1816952_hom C Y Z.
        compose C h (compose C g f) = compose C (compose C h g) f)"

definition q1816952_is_preadditive ::
    "('o, 'm, 'k) q1816952_linear_category_data \<Rightarrow> bool" where
  "q1816952_is_preadditive C \<longleftrightarrow>
    q1816952_is_category C \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      zero_arrow C X Y \<in> q1816952_hom C X Y \<and>
      (\<forall>f \<in> q1816952_hom C X Y.
        neg_arrow C f \<in> q1816952_hom C X Y) \<and>
      (\<forall>f \<in> q1816952_hom C X Y.
        \<forall>g \<in> q1816952_hom C X Y.
          add_arrow C f g \<in> q1816952_hom C X Y) \<and>
      (\<forall>f \<in> q1816952_hom C X Y.
        add_arrow C (zero_arrow C X Y) f = f \<and>
        add_arrow C f (zero_arrow C X Y) = f) \<and>
      (\<forall>f \<in> q1816952_hom C X Y.
        add_arrow C f (neg_arrow C f) = zero_arrow C X Y) \<and>
      (\<forall>f \<in> q1816952_hom C X Y.
        \<forall>g \<in> q1816952_hom C X Y.
          add_arrow C f g = add_arrow C g f) \<and>
      (\<forall>f \<in> q1816952_hom C X Y.
        \<forall>g \<in> q1816952_hom C X Y.
        \<forall>h \<in> q1816952_hom C X Y.
          add_arrow C (add_arrow C f g) h =
            add_arrow C f (add_arrow C g h))) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C. \<forall>Z \<in> objects C.
      \<forall>f \<in> q1816952_hom C X Y.
      \<forall>g \<in> q1816952_hom C X Y.
      \<forall>h \<in> q1816952_hom C Y Z.
        compose C h (add_arrow C f g) =
          add_arrow C (compose C h f) (compose C h g)) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C. \<forall>Z \<in> objects C.
      \<forall>f \<in> q1816952_hom C X Y.
      \<forall>g \<in> q1816952_hom C Y Z.
      \<forall>h \<in> q1816952_hom C Y Z.
        compose C (add_arrow C g h) f =
          add_arrow C (compose C g f) (compose C h f))"

definition q1816952_is_linear_category ::
    "('o, 'm, 'k::field) q1816952_linear_category_data \<Rightarrow> bool" where
  "q1816952_is_linear_category C \<longleftrightarrow>
    q1816952_is_preadditive C \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      (\<forall>a. \<forall>f \<in> q1816952_hom C X Y.
        scalar_arrow C a f \<in> q1816952_hom C X Y) \<and>
      (\<forall>f \<in> q1816952_hom C X Y.
        scalar_arrow C 0 f = zero_arrow C X Y \<and>
        scalar_arrow C 1 f = f) \<and>
      (\<forall>a b. \<forall>f \<in> q1816952_hom C X Y.
        scalar_arrow C (a + b) f =
          add_arrow C (scalar_arrow C a f) (scalar_arrow C b f)) \<and>
      (\<forall>a. \<forall>f \<in> q1816952_hom C X Y.
        \<forall>g \<in> q1816952_hom C X Y.
          scalar_arrow C a (add_arrow C f g) =
            add_arrow C (scalar_arrow C a f) (scalar_arrow C a g)) \<and>
      (\<forall>a b. \<forall>f \<in> q1816952_hom C X Y.
        scalar_arrow C (a * b) f =
          scalar_arrow C a (scalar_arrow C b f))) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C. \<forall>Z \<in> objects C.
      \<forall>a. \<forall>f \<in> q1816952_hom C X Y.
      \<forall>g \<in> q1816952_hom C Y Z.
        compose C g (scalar_arrow C a f) =
          scalar_arrow C a (compose C g f) \<and>
        compose C (scalar_arrow C a g) f =
          scalar_arrow C a (compose C g f))"

definition q1816952_is_algebraically_closed ::
    "'k::field itself \<Rightarrow> bool" where
  "q1816952_is_algebraically_closed _ \<longleftrightarrow>
    (\<forall>c :: nat \<Rightarrow> 'k.
      finite {n. c n \<noteq> 0} \<longrightarrow>
      (\<exists>n>0. c n \<noteq> 0) \<longrightarrow>
      (\<exists>x. (\<Sum>n\<in>{n. c n \<noteq> 0}. c n * x ^ n) = 0))"

definition q1816952_is_kernel ::
    "('o, 'm, 'k) q1816952_linear_category_data \<Rightarrow>
      'm \<Rightarrow> 'm \<Rightarrow> bool" where
  "q1816952_is_kernel C k f \<longleftrightarrow>
    k \<in> arrows C \<and> f \<in> arrows C \<and>
    target C k = source C f \<and>
    compose C f k = zero_arrow C (source C k) (target C f) \<and>
    (\<forall>X \<in> objects C. \<forall>h \<in> q1816952_hom C X (source C f).
      compose C f h = zero_arrow C X (target C f) \<longrightarrow>
      (\<exists>!u.
        u \<in> q1816952_hom C X (source C k) \<and>
        compose C k u = h))"

definition q1816952_has_kernels ::
    "('o, 'm, 'k) q1816952_linear_category_data \<Rightarrow> bool" where
  "q1816952_has_kernels C \<longleftrightarrow>
    (\<forall>f \<in> arrows C. \<exists>k. q1816952_is_kernel C k f)"

definition q1816952_is_monomorphism ::
    "('o, 'm, 'k) q1816952_linear_category_data \<Rightarrow>
      'm \<Rightarrow> bool" where
  "q1816952_is_monomorphism C f \<longleftrightarrow>
    f \<in> arrows C \<and>
    (\<forall>X \<in> objects C.
      \<forall>g \<in> q1816952_hom C X (source C f).
      \<forall>h \<in> q1816952_hom C X (source C f).
        compose C f g = compose C f h \<longrightarrow> g = h)"

definition q1816952_is_isomorphism ::
    "('o, 'm, 'k) q1816952_linear_category_data \<Rightarrow>
      'm \<Rightarrow> bool" where
  "q1816952_is_isomorphism C f \<longleftrightarrow>
    f \<in> arrows C \<and>
    (\<exists>g \<in> q1816952_hom C (target C f) (source C f).
      compose C g f = identity C (source C f) \<and>
      compose C f g = identity C (target C f))"

definition q1816952_is_simple_object ::
    "('o, 'm, 'k) q1816952_linear_category_data \<Rightarrow>
      'o \<Rightarrow> bool" where
  "q1816952_is_simple_object C X \<longleftrightarrow>
    X \<in> objects C \<and>
    identity C X \<noteq> zero_arrow C X X \<and>
    (\<forall>Y \<in> objects C. \<forall>f \<in> q1816952_hom C Y X.
      q1816952_is_monomorphism C f \<longrightarrow>
        f = zero_arrow C Y X \<or> q1816952_is_isomorphism C f)"

fun q1816952_end_lincomb ::
    "('o, 'm, 'k) q1816952_linear_category_data \<Rightarrow>
      'o \<Rightarrow> ('k \<times> 'm) list \<Rightarrow> 'm" where
  "q1816952_end_lincomb C X [] = zero_arrow C X X"
| "q1816952_end_lincomb C X ((a, f) # xs) =
    add_arrow C (scalar_arrow C a f) (q1816952_end_lincomb C X xs)"

definition q1816952_finite_dimensional_end ::
    "('o, 'm, 'k::field) q1816952_linear_category_data \<Rightarrow>
      'o \<Rightarrow> bool" where
  "q1816952_finite_dimensional_end C X \<longleftrightarrow>
    (\<exists>B :: 'm list.
      set B \<subseteq> q1816952_hom C X X \<and>
      (\<forall>f \<in> q1816952_hom C X X.
        \<exists>cs :: 'k list.
          length cs = length B \<and>
          q1816952_end_lincomb C X (zip cs B) = f))"

theorem q1816952_schur_s_lemma:
  fixes C :: "('o, 'm, 'k::field) q1816952_linear_category_data"
    and X :: 'o
  assumes "q1816952_is_linear_category C"
    and "q1816952_is_algebraically_closed (TYPE('k))"
    and "q1816952_has_kernels C"
    and "q1816952_is_simple_object C X"
    and "q1816952_finite_dimensional_end C X"
  shows "\<forall>f \<in> q1816952_hom C X X.
    \<exists>!c :: 'k. scalar_arrow C c (identity C X) = f"
  sorry

end
