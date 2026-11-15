(*
  Statement-only formalization of thousand-theorems corpus artifact Q22952648
  (thousand-theorems__isabelle__Q22952648), "Uncountability of the continuum":
  there is no surjection from the natural numbers onto the real numbers. This
  file contains no proof.
*)

theory Q22952648_uncountability_of_the_continuum
  imports Complex_Main
begin

theorem q22952648_not_countable_real:
  "\<nexists>f :: nat \<Rightarrow> real. surj f"
  sorry

end
