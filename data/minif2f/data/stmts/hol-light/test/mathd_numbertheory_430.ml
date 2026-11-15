(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_430. This file
  contains no proof.
*)

let statement = `!a b c:num.
  (1 <= a /\ a <= 9) /\
  (1 <= b /\ b <= 9) /\
  (1 <= c /\ c <= 9) /\
  ~(a = b) /\
  ~(a = c) /\
  ~(b = c) /\
  a + b = c /\
  10 * a + a - b = 2 * c /\
  c * b = 10 * a + a + a
  ==> a + b + c = 8`;;
