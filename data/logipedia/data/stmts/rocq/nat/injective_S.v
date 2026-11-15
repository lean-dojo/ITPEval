(*
  Statement-only formalization of Logipedia corpus artifact nat.injective_S
  (catalog title "nat.injective_S"): the successor function on natural
  numbers is injective. This file contains no proof.
*)

Theorem logipedia_nat_injective_S :
  forall x y : nat,
    S x = S y ->
    x = y.
Admitted.
