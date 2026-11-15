(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1506253,
  "Euclid's theorem": for every natural number n, there is a prime natural
  number p with n <= p. This file contains no proof.
*)

let Q1506253_EUCLIDS_THEOREM =
  `!n:num. ?p:num. n <= p /\ prime p`;;
