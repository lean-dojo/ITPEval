(*
  Statement-only formalization of miniF2F valid problem aime_1987_p8. This file contains no
  proof.
*)

let statement =
  `(0 < (112:num) /\
    (?!k:num.
       &8 / &15 < &112 / &(112 + k) /\
       &112 / &(112 + k) < &7 / &13)) /\
   (!n:num.
      (0 < n /\
       (?!k:num.
          &8 / &15 < &n / &(n + k) /\
          &n / &(n + k) < &7 / &13))
      ==> n <= 112)`;;
