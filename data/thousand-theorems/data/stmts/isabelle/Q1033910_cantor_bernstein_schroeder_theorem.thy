(*
  Statement-only formalization of thousand-theorems corpus artifact Q1033910,
  "Cantor–Bernstein–Schroeder theorem": injections from each of two arbitrary
  sets into the other imply that the sets are in bijection. This file contains
  no proof.
*)

theory Q1033910_cantor_bernstein_schroeder_theorem
  imports Main
begin

theorem cantor_bernstein_schroeder:
  fixes A :: "'a set"
    and B :: "'b set"
    and f :: "'a \<Rightarrow> 'b"
    and g :: "'b \<Rightarrow> 'a"
  assumes "f ` A \<subseteq> B"
    and "inj_on f A"
    and "g ` B \<subseteq> A"
    and "inj_on g B"
  shows "\<exists>h :: 'a \<Rightarrow> 'b. bij_betw h A B"
  sorry

end
