(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.eq_to_bijn, catalog title "permutation.eq_to_bijn": bounded
  surjectivity on the natural-number segment from zero through n is preserved
  when two natural-number functions agree at every input in that segment.
  This file contains no proof.
*)

theory eq_to_bijn
  imports Main
begin

definition logipedia_bijn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
  where
    "logipedia_bijn f n \<longleftrightarrow>
      (\<forall>m :: nat. m \<le> n \<longrightarrow>
        (\<exists>p :: nat. p \<le> n \<and> f p = m))"

theorem eq_to_bijn:
  fixes f g :: "nat \<Rightarrow> nat"
    and n :: nat
  assumes "\<forall>i :: nat. i \<le> n \<longrightarrow> f i = g i"
    and "logipedia_bijn f n"
  shows "logipedia_bijn g n"
  sorry

end
