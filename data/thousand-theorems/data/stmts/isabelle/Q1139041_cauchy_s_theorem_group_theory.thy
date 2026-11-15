(*
  Statement-only formalization of thousand-theorems corpus artifact Q1139041,
  "Cauchy's theorem (group theory)": if a prime divides the order of a finite
  group, then the group contains an element of that prime order.
  This file contains no proof.
*)

theory Q1139041_cauchy_s_theorem_group_theory
  imports "HOL-Algebra.Multiplicative_Group"
begin

theorem (in group) exists_prime_orderOf_dvd_card:
  fixes p :: nat
  assumes finite_group: "finite (carrier G)"
    and prime_p: "prime p"
    and divides_order: "p dvd order G"
  shows "\<exists>x \<in> carrier G. ord x = p"
  oops

end
