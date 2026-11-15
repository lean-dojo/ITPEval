(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.bijn_fg, catalog title "permutation.bijn_fg": bounded
  surjectivity onto the naturals from zero through n is preserved under
  composition of two natural-number functions. This file contains no proof.
*)

theory bijn_fg
  imports Main
begin

definition logipedia_bijn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
  where
    "logipedia_bijn f n \<longleftrightarrow>
      (\<forall>m. m \<le> n \<longrightarrow> (\<exists>p. p \<le> n \<and> f p = m))"

theorem bijn_fg:
  fixes f g :: "nat \<Rightarrow> nat"
    and n :: nat
  assumes "logipedia_bijn f n"
    and "logipedia_bijn g n"
  shows "logipedia_bijn (\<lambda>p. f (g p)) n"
  sorry

end
