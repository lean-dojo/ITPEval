(*
  miniF2F valid artifact imo_1967_p3: for positive natural numbers k, m,
  and n with k + m + 1 prime and n + 1 < k + m + 1, if c(s) = s(s + 1),
  then the product of c over 1..n divides the product of c(m+i) - c(k)
  over i in 1..n. This is a statement-only formalization and contains no proof.
*)

let statement =
  `!k m n:num. !c:num->num.
     0 < k /\ 0 < m /\ 0 < n /\
     (!s:num. c s = s * (s + 1)) /\
     prime (k + m + 1) /\
     n + 1 < k + m + 1
     ==> iproduct (1..n) (\i:num. &(c i)) divides
         iproduct (1..n) (\i:num. &(c (m + i)) - &(c k))`;;
