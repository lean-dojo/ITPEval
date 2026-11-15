(*
  Statement-only formalization of thousand-theorems corpus artifact Q536640
  (thousand-theorems__isabelle__Q536640), "Hall's marriage theorem": an indexed
  family of finite sets has an injective system of representatives exactly when
  every finite subfamily has a union at least as large as its index set. This
  file contains no proof.
*)

theory Q536640_hall_s_marriage_theorem
  imports Main
begin

theorem hall_marriage:
  fixes t :: "'i \<Rightarrow> 'a set"
  assumes finite_values: "\<And>i. finite (t i)"
  shows
    "(\<forall>S :: 'i set. finite S \<longrightarrow>
        card S \<le> card (\<Union>i\<in>S. t i)) \<longleftrightarrow>
      (\<exists>f :: 'i \<Rightarrow> 'a.
        inj f \<and> (\<forall>i. f i \<in> t i))"
  sorry

end
