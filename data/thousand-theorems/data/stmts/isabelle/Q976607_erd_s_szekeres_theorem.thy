(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q976607 (thousand-theorems__isabelle__Q976607), "Erdős–Szekeres theorem":
  a sufficiently long injective sequence in a linear order has an increasing
  subsequence longer than r or a decreasing subsequence longer than s.
  This file contains no proof.
*)

theory Q976607_erd_s_szekeres_theorem
  imports Main
begin

theorem erdos_szekeres:
  fixes r s :: nat
    and f :: "'a::{finite,linorder} \<Rightarrow> 'b::linorder"
  assumes length_bound: "r * s < card (UNIV :: 'a set)"
    and injective: "inj f"
  shows "(\<exists>T :: 'a set. r < card T \<and> strict_mono_on T f) \<or>
    (\<exists>T :: 'a set. s < card T \<and> strict_antimono_on T f)"
  sorry

end
