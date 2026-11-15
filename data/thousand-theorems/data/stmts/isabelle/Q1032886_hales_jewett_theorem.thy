(*
  Statement-only formalization of thousand-theorems corpus artifact Q1032886
  (thousand-theorems__isabelle__Q1032886), "Hales–Jewett theorem": for every
  finite alphabet and finite color set, every coloring of sufficiently
  high-dimensional words has a monochromatic combinatorial line. This file
  contains no proof.
*)

theory Q1032886_hales_jewett_theorem
  imports Main
begin

definition q1032886_words ::
    "'a set \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "q1032886_words alphabet n =
    {w. length w = n \<and> set w \<subseteq> alphabet}"

definition q1032886_line_word ::
    "'a option list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "q1032886_line_word pattern x =
    map (\<lambda>entry. case entry of None \<Rightarrow> x | Some a \<Rightarrow> a) pattern"

definition q1032886_line ::
    "'a set \<Rightarrow> nat \<Rightarrow> 'a option list \<Rightarrow> bool" where
  "q1032886_line alphabet n pattern \<longleftrightarrow>
    length pattern = n \<and>
    None \<in> set pattern \<and>
    set pattern \<subseteq> insert None (Some ` alphabet)"

definition q1032886_coloring ::
    "'a set \<Rightarrow> 'c set \<Rightarrow> nat \<Rightarrow>
      ('a list \<times> 'c) set \<Rightarrow> bool" where
  "q1032886_coloring alphabet colors n C \<longleftrightarrow>
    (\<forall>w \<in> q1032886_words alphabet n.
      \<exists>!c. c \<in> colors \<and> (w, c) \<in> C) \<and>
    (\<forall>w c. (w, c) \<in> C \<longrightarrow>
      w \<in> q1032886_words alphabet n \<and> c \<in> colors)"

theorem q1032886_hales_jewett:
  fixes alphabet :: "'a set"
    and colors :: "'c set"
  assumes finite_alphabet: "finite alphabet"
    and finite_colors: "finite colors"
  shows "\<exists>n. \<forall>C :: ('a list \<times> 'c) set.
    q1032886_coloring alphabet colors n C \<longrightarrow>
      (\<exists>pattern c.
        q1032886_line alphabet n pattern \<and>
        c \<in> colors \<and>
        (\<forall>x \<in> alphabet. (q1032886_line_word pattern x, c) \<in> C))"
  sorry

end
