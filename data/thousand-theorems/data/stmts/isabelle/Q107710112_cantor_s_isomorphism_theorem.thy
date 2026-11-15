(*
  Statement-only formalization of thousand-theorems corpus artifact Q107710112,
  "Cantor's isomorphism theorem": any two countable, nonempty, dense linear
  orders without endpoints are order-isomorphic. This file contains no proof.
*)

theory Q107710112_cantor_s_isomorphism_theorem
  imports Main
begin

theorem cantor_isomorphism:
  assumes countable_a: "\<exists>e :: 'a::linorder \<Rightarrow> nat. inj e"
    and dense_a:
      "\<forall>x y :: 'a. x < y \<longrightarrow> (\<exists>z. x < z \<and> z < y)"
    and no_min_a: "\<forall>x :: 'a. \<exists>y. y < x"
    and no_max_a: "\<forall>x :: 'a. \<exists>y. x < y"
    and countable_b: "\<exists>e :: 'b::linorder \<Rightarrow> nat. inj e"
    and dense_b:
      "\<forall>x y :: 'b. x < y \<longrightarrow> (\<exists>z. x < z \<and> z < y)"
    and no_min_b: "\<forall>x :: 'b. \<exists>y. y < x"
    and no_max_b: "\<forall>x :: 'b. \<exists>y. x < y"
  shows "\<exists>f :: 'a \<Rightarrow> 'b.
    bij f \<and> (\<forall>x y. x < y \<longleftrightarrow> f x < f y)"
  sorry

end
