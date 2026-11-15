(*
  Statement-only formalization of thousand-theorems corpus artifact Q188295
  (thousand-theorems__isabelle__Q188295), "Fermat's little theorem": every
  nonzero residue modulo a prime p has (p - 1)-st power equal to one.
  This file contains no proof.
*)

theory Q188295_fermat_s_little_theorem
  imports Main
begin

theorem fermat_s_little_theorem:
  fixes p a :: nat
  assumes "prime p"
    and "\<not> p dvd a"
  shows "a ^ (p - 1) mod p = 1"
  sorry

end
