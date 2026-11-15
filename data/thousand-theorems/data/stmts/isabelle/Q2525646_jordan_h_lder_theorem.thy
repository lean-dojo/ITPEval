(*
  Statement-only formalization of thousand-theorems corpus artifact Q2525646,
  "Jordan–Hölder theorem": composition series with the same least and greatest
  terms are equivalent up to a bijection preserving the factor relation.
  This file contains no proof.
*)

theory Q2525646_jordan_h_lder_theorem
  imports Main
begin

type_synonym 'a q2525646_series = "nat \<times> (nat \<Rightarrow> 'a)"

definition q2525646_length :: "'a q2525646_series \<Rightarrow> nat" where
  "q2525646_length s = fst s"

definition q2525646_term :: "'a q2525646_series \<Rightarrow> nat \<Rightarrow> 'a" where
  "q2525646_term s = snd s"

definition q2525646_head :: "'a q2525646_series \<Rightarrow> 'a" where
  "q2525646_head s = q2525646_term s 0"

definition q2525646_last :: "'a q2525646_series \<Rightarrow> 'a" where
  "q2525646_last s = q2525646_term s (q2525646_length s)"

definition q2525646_composition_series ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a q2525646_series \<Rightarrow> bool" where
  "q2525646_composition_series IsMaximal s \<longleftrightarrow>
    (\<forall>i < q2525646_length s.
      IsMaximal (q2525646_term s i) (q2525646_term s (Suc i)))"

definition q2525646_equivalent ::
    "(('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool) \<Rightarrow>
      'a q2525646_series \<Rightarrow> 'a q2525646_series \<Rightarrow> bool" where
  "q2525646_equivalent Iso s1 s2 \<longleftrightarrow>
    (\<exists>f :: nat \<Rightarrow> nat.
      bij_betw f {..<q2525646_length s1} {..<q2525646_length s2} \<and>
      (\<forall>i < q2525646_length s1.
        Iso (q2525646_term s1 i, q2525646_term s1 (Suc i))
          (q2525646_term s2 (f i), q2525646_term s2 (Suc (f i)))))"

locale q2525646_jordan_holder_lattice =
  fixes IsMaximal :: "'a::lattice \<Rightarrow> 'a \<Rightarrow> bool"
    and Iso :: "('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool"
  assumes lt_of_isMaximal:
      "IsMaximal x y \<Longrightarrow> x < y"
    and sup_eq_of_isMaximal:
      "\<lbrakk>IsMaximal x z; IsMaximal y z; x \<noteq> y\<rbrakk> \<Longrightarrow> sup x y = z"
    and isMaximal_inf_left_of_isMaximal_sup:
      "\<lbrakk>IsMaximal x (sup x y); IsMaximal y (sup x y)\<rbrakk>
        \<Longrightarrow> IsMaximal (inf x y) x"
    and iso_symm:
      "Iso p q \<Longrightarrow> Iso q p"
    and iso_trans:
      "\<lbrakk>Iso p q; Iso q r\<rbrakk> \<Longrightarrow> Iso p r"
    and second_iso:
      "IsMaximal x (sup x y)
        \<Longrightarrow> Iso (x, sup x y) (inf x y, y)"
begin

theorem q2525646_jordan_holder:
  assumes series1: "q2525646_composition_series IsMaximal s1"
    and series2: "q2525646_composition_series IsMaximal s2"
    and same_head: "q2525646_head s1 = q2525646_head s2"
    and same_last: "q2525646_last s1 = q2525646_last s2"
  shows "q2525646_equivalent Iso s1 s2"
  sorry

end

end
