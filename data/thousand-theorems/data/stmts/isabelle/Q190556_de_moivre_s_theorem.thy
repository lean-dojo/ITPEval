(*
  Statement-only formalization of the thousand-theorems corpus artifact Q190556
  (thousand-theorems__isabelle__Q190556), "De Moivre's theorem": for every
  natural exponent and complex argument, the corresponding power of cosine
  plus sine times the imaginary unit equals the same expression at the
  exponent-scaled argument. This file contains no proof.
*)

theory Q190556_de_moivre_s_theorem
  imports Complex_Main
begin

theorem de_moivre_s_theorem:
  fixes n :: nat
    and z :: complex
  shows "(cos z + sin z * \<i>) ^ n =
    cos (of_nat n * z) + sin (of_nat n * z) * \<i>"
  sorry

end
