(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1227703
  (thousand-theorems__hol-light__Q1227703), "Dirichlet's approximation
  theorem": on a real circle of positive circumference, every point has a
  multiple indexed from one through n whose distance to zero is at most the
  circumference divided by n + 1. This file contains no proof.
*)

let Q1227703_DIRICHLETS_APPROXIMATION_THEOREM =
  `!T x:real n:num.
     &0 < T /\ 0 < n
     ==> ?j:num m:int.
           1 <= j /\ j <= n /\
           abs(&j * x - real_of_int m * T) <= T / &(n + 1)`;;
