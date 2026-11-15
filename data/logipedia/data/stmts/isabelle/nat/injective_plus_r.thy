(*
  Statement-only formalization of Logipedia corpus artifact
  nat.injective_plus_r, catalog title "nat.injective_plus_r": for every
  natural number n, adding n on the left defines an injective function of the
  right summand. This file contains no proof.
*)

theory injective_plus_r
  imports Main
begin

theorem injective_plus_r:
  "\<forall>n :: nat. inj (\<lambda>m :: nat. n + m)"
  sorry

end
