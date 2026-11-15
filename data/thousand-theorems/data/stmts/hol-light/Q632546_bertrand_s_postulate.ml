(*
  Statement-only formalization of Thousand Theorems corpus artifact Q632546,
  "Bertrand's postulate": for every nonzero natural number n, there exists a
  prime natural number p strictly greater than n and at most twice n. This file
  contains no proof.
*)

let Q632546_BERTRANDS_POSTULATE =
  `!n:num. ~(n = 0) ==> ?p:num. prime p /\ n < p /\ p <= 2 * n`;;
