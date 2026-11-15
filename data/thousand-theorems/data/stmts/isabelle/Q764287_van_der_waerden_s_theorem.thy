(*
  Statement-only formalization of thousand-theorems corpus artifact Q764287
  (thousand-theorems__isabelle__Q764287), "Van der Waerden's theorem":
  every finite coloring of an additive commutative monoid has a monochromatic
  positive homothetic copy of each finite subset. This file contains no proof.
*)

theory Q764287_van_der_waerden_s_theorem
  imports Main
begin

primrec q764287_nsmult ::
    "nat \<Rightarrow> 'a::comm_monoid_add \<Rightarrow> 'a" where
  "q764287_nsmult 0 x = 0"
| "q764287_nsmult (Suc n) x = q764287_nsmult n x + x"

theorem van_der_waerden_homothetic_copy:
  fixes S :: "'a::comm_monoid_add set"
    and C :: "'a \<Rightarrow> 'c::finite"
  assumes "finite S"
  shows "\<exists>n::nat. n > 0 \<and>
    (\<exists>b::'a. \<exists>c::'c.
      \<forall>s\<in>S. C (q764287_nsmult n s + b) = c)"
  sorry

end
