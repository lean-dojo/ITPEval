(*
  Statement-only formalization of Thousand Theorems corpus artifact Q420714,
  "Akra–Bazzi theorem": an Akra–Bazzi divide-and-conquer recurrence is
  asymptotically bounded above by its discrete sum-transform expression.
  This file contains no proof.
*)

needs "Library/transc.ml";;

let Q420714_AKRA_BAZZI_THEOREM =
 `let real_rpow =
      \(x:real) (q:real).
        if x = &0
        then if q = &0 then &1 else &0
        else exp(q * ln x) in
   let grows_polynomially =
      \(g:real->real).
        !beta:real.
          &0 < beta /\ beta < &1
          ==> ?c1 c2 threshold:real.
                &0 < c1 /\ &0 < c2 /\
                !x u:real.
                  threshold <= x /\
                  beta * x <= u /\ u <= x
                  ==> c1 * g x <= g u /\ g u <= c2 * g x in
   let little_o_sequence =
      \(f:num->real) (h:num->real).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num.
                !n:num.
                  N <= n ==> abs(f n) <= epsilon * abs(h n) in
   let big_o_sequence =
      \(f:num->real) (h:num->real).
        ?C:real. ?N:num.
          &0 < C /\
          !n:num. N <= n ==> abs(f n) <= C * abs(h n) in
   let akra_exponent =
      \(a:A->real) (b:A->real).
        @p:real.
          sum (:A) (\i:A. a i * real_rpow (b i) p) = &1 in
   let asymp_bound =
      \(g:real->real) (a:A->real) (b:A->real) (n:num).
        let p = akra_exponent a b in
        real_rpow (&n) p *
        (&1 +
         sum {u:num | u < n}
           (\u:num. g (&u) / real_rpow (&u) (p + &1))) in
   !cost:num->real.
   !g:real->real.
   !a b:A->real.
   !r:A->num->num.
   !n0:num.
     FINITE (:A) /\
     0 < n0 /\
     (!i:A. &0 < a i) /\
     (!i:A. &0 < b i) /\
     (!i:A. b i < &1) /\
     (!x:real. &0 <= x ==> &0 <= g x) /\
     grows_polynomially g /\
     (!n:num.
        n0 <= n
        ==> cost n =
            sum (:A) (\i:A. a i * cost (r i n)) + g (&n)) /\
     (!n:num. n < n0 ==> &0 < cost n) /\
     (!i:A. !n:num. n0 <= n ==> r i n < n) /\
     (!i:A.
        little_o_sequence
          (\n:num. &(r i n) - b i * &n)
          (\n:num. &n / (ln(&n) pow 2)))
     ==> big_o_sequence cost (asymp_bound g a b)`;;
