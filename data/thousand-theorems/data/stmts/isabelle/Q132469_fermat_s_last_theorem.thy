(*
  Statement-only formalization of thousand-theorems corpus artifact Q132469
  (thousand-theorems__isabelle__Q132469), "Fermat's Last Theorem": for every
  natural exponent at least three, no three nonzero natural numbers satisfy
  the Fermat equation. This file contains no proof.
*)

theory Q132469_fermat_s_last_theorem
  imports Main
begin

theorem FermatLastTheorem:
  "\<forall>n::nat. 3 \<le> n \<longrightarrow>
    (\<forall>a b c::nat.
      a \<noteq> 0 \<longrightarrow>
      b \<noteq> 0 \<longrightarrow>
      c \<noteq> 0 \<longrightarrow>
      a ^ n + b ^ n \<noteq> c ^ n)"
  sorry

end
