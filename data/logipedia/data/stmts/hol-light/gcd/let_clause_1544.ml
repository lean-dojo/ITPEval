(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1544, catalog title "gcd.let_clause_1544": a natural-number
  induction-step clause for a Bezout-style characterization of the recursive
  greatest-common-divisor auxiliary function, with the concluding equality
  differing only by the order of a product. This file contains no proof.
*)

let logipedia_gcd_gcd_aux = new_recursive_definition num_RECURSION
  `(logipedia_gcd_gcd_aux 0 m n = m) /\
   (logipedia_gcd_gcd_aux (SUC p) m n =
      if m MOD n = 0 then n
      else logipedia_gcd_gcd_aux p n (m MOD n))`;;

let statement =
  `!p:num. !q:num.
     (!m n:num.
        0 < n
        ==> n <= m
        ==> n <= q
        ==> ?a b:num.
              a * n - b * m = logipedia_gcd_gcd_aux q m n \/
              b * m - a * n = logipedia_gcd_gcd_aux q m n)
     ==> !m n:num.
           0 < n
           ==> n <= m
           ==> n <= SUC q
           ==> ~(n divides m)
           ==> !a:num.
                 (?b:num.
                    a * (m MOD n) - b * n =
                      logipedia_gcd_gcd_aux q n (m MOD n) \/
                    b * n - a * (m MOD n) =
                      logipedia_gcd_gcd_aux q n (m MOD n))
                 ==> !b:num.
                       (a * (m MOD n) - b * n =
                          logipedia_gcd_gcd_aux q n (m MOD n) \/
                        b * n - a * (m MOD n) =
                          logipedia_gcd_gcd_aux q n (m MOD n))
                       ==> a * (m MOD n) - b * n =
                             logipedia_gcd_gcd_aux q n (m MOD n)
                       ==> a * (m MOD n) - n * b =
                             logipedia_gcd_gcd_aux q n (m MOD n)`;;
