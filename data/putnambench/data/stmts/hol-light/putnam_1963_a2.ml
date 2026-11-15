(*
  Statement-only formalization of PutnamBench artifact putnam_1963_a2:
  a strictly increasing positive-integer-valued multiplicative function
  normalized by f(2) = 2 is the identity. This file contains no proof.
*)

let statement =
  `!f:num->num.
     (!n. 0 < f n) /\
     (!i j. 0 < i /\ i < j ==> f i < f j) /\
     f 2 = 2 /\
     (!m n.
        0 < m /\ 0 < n /\ coprime(m,n)
        ==> f (m * n) = f m * f n)
     ==> !n. 0 < n ==> f n = n`;;
