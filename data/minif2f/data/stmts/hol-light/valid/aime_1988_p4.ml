(*
  Statement-only formalization of miniF2F valid artifact aime_1988_p4:
  a bounded real sequence satisfying the given absolute-sum identity has
  length at least 20. This file contains no proof.
*)

let statement = `!n:num a:num->real.
    (!k:num. abs (a k) < &1) /\
    sum (0..(n - 1)) (\k. abs (a k)) =
      &19 + abs (sum (0..(n - 1)) a)
    ==> 20 <= n`;;
