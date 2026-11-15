(*
  Statement-only formalization of thousand-theorems corpus artifact Q1259814,
  "Nielsen–Schreier theorem": every subgroup of a free group is itself a free
  group, expressed by the equivalent unique reduced-word characterization of
  a free basis. This file contains no proof.
*)

theory Q1259814_nielsen_schreier_theorem
  imports "HOL-Algebra.Group"
begin

datatype 'g q1259814_letter =
    Q1259814_Pos 'g
  | Q1259814_Neg 'g

fun q1259814_letter_base :: "'g q1259814_letter \<Rightarrow> 'g" where
  "q1259814_letter_base (Q1259814_Pos x) = x"
| "q1259814_letter_base (Q1259814_Neg x) = x"

fun q1259814_inverse_letter ::
    "'g q1259814_letter \<Rightarrow> 'g q1259814_letter" where
  "q1259814_inverse_letter (Q1259814_Pos x) = Q1259814_Neg x"
| "q1259814_inverse_letter (Q1259814_Neg x) = Q1259814_Pos x"

fun q1259814_letter_value ::
    "('g, 'm) monoid_scheme \<Rightarrow> 'g q1259814_letter \<Rightarrow> 'g" where
  "q1259814_letter_value G (Q1259814_Pos x) = x"
| "q1259814_letter_value G (Q1259814_Neg x) = inv\<^bsub>G\<^esub> x"

fun q1259814_word_value ::
    "('g, 'm) monoid_scheme \<Rightarrow> 'g q1259814_letter list \<Rightarrow> 'g" where
  "q1259814_word_value G [] = \<one>\<^bsub>G\<^esub>"
| "q1259814_word_value G (l # w) =
    q1259814_letter_value G l \<otimes>\<^bsub>G\<^esub> q1259814_word_value G w"

fun q1259814_reduced ::
    "'g set \<Rightarrow> 'g q1259814_letter list \<Rightarrow> bool" where
  "q1259814_reduced B [] = True"
| "q1259814_reduced B [l] = (q1259814_letter_base l \<in> B)"
| "q1259814_reduced B (l # k # w) =
    (q1259814_letter_base l \<in> B \<and>
     k \<noteq> q1259814_inverse_letter l \<and>
     q1259814_reduced B (k # w))"

definition q1259814_is_free_subgroup ::
    "('g, 'm) monoid_scheme \<Rightarrow> 'g set \<Rightarrow> bool" where
  "q1259814_is_free_subgroup G H \<longleftrightarrow>
    subgroup H G \<and>
    (\<exists>B \<subseteq> H. \<forall>x \<in> H. \<exists>!w.
      q1259814_reduced B w \<and> q1259814_word_value G w = x)"

theorem (in group) subgroupIsFreeOfIsFree:
  assumes "q1259814_is_free_subgroup G (carrier G)"
    and "subgroup H G"
  shows "q1259814_is_free_subgroup G H"
  sorry

end
