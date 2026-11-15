(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b3
  (putnambench__hol-light__putnam_2023_b3): the expected maximum length of a
  zigzag subsequence of independent uniform samples from the unit interval.
  This file contains no proof.
*)

needs "Library/transc.ml";;

let statement =
  `let zigzag =
     \(ys:real list).
       LENGTH ys = 1 \/
       (2 <= LENGTH ys /\
        (!i:num.
           i + 1 < LENGTH ys
           ==> ~(EL (i + 1) ys = EL i ys)) /\
        (!i:num.
           i + 2 < LENGTH ys
           ==> (EL (i + 2) ys < EL (i + 1) ys <=>
                EL i ys < EL (i + 1) ys))) in
   let increasing_indices =
     \(n:num) (is:num list).
       (!i:num. i < LENGTH is ==> EL i is < n) /\
       (!i j:num.
          i < j /\ j < LENGTH is
          ==> EL i is < EL j is) in
   let admissible_lengths =
     \(n:num) (x:real list).
       {k:num |
          ?is:num list.
            LENGTH is = k /\
            increasing_indices n is /\
            zigzag (MAP (\i:num. EL i x) is)} in
   let greatest =
     \(s:num->bool) (k:num).
       k IN s /\ (!j:num. j IN s ==> j <= k) in
   let unit_sample =
     \(n:num) (x:real list).
       LENGTH x = n /\
       (!i:num. i < n ==> &0 <= EL i x /\ EL i x <= &1) in
   let cube_integral =
     \(n:num) (f:real list->real).
       ITLIST
         (\u:bool. \(g:real list->real). \(prefix:real list).
            integral(&0,&1)
              (\t:real. g (APPEND prefix [t])))
         (REPLICATE n T) f [] in
   !n:num. !a:real list->num.
     2 <= n /\
     (!x:real list.
        unit_sample n x
        ==> greatest (admissible_lengths n x) (a x))
     ==>
     cube_integral n (\x:real list. &(a x)) =
       (&2 * &n + &2) / &3`;;
