(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b2:
  the attainable total costs of finite rightward jumps from zero to one are
  exactly the real interval (1/3, 1]. This file contains no proof.
*)

let statement =
  `{c:real |
      ?s:num->real.
        s 0 = &0 /\
        (!i j:num. i < j ==> s i < s j) /\
        ?n:num.
          s n = &1 /\
          sum (0..n - 1)
              (\i:num.
                 (s (i + 1)) pow 3 -
                 s i * (s (i + 1)) pow 2) = c} =
   {c:real | &1 / &3 < c /\ c <= &1}`;;
