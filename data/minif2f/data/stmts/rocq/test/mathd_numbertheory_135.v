Require Import Nat.
Require Import List.
Import ListNotations.

(*
  Statement-only formalization of miniF2F test problem
  mathd_numbertheory_135: the decimal expansion ABCACCBAB determines
  100A + 10B + C.
*)

Theorem mathd_numbertheory_135 
  (n A B C : nat)
  (H0 : n = 3^17 + 3^10)
  (H1 : exists k, n + 1 = 11 * k)
  (H2 : A <> B /\ B <> C /\ A <> C)
  (H3 : A <= 9 /\ B <= 9 /\ C <= 9)
  (H4 : Nat.odd A = true /\ Nat.odd C = true)
  (H5 : ~(exists k, B = 3 * k))
  (H6 : n = A * 10^8 + B * 10^7 + C * 10^6 + A * 10^5 + C * 10^4 +
          C * 10^3 + B * 10^2 + A * 10 + B) :
  100 * A + 10 * B + C = 129.

Proof.
