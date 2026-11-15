(*
  Authors: Wenda Li
*)

theory induction_divisibility_3div2tooddnp1
 imports
  Complex_Main
begin

theorem induction_divisibility_3div2tooddnp1:
  fixes n ::nat
  shows "(3::nat) dvd (2^(2 * n + 1) + 1)"
  by sorry

end 
