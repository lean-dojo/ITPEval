(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a4
  (putnambench__hol-light__putnam_2018_a4): floor-difference exponents in an
  ordered product in an arbitrary group force the two group elements to
  commute. This file contains no proof.
*)

needs "Library/floor.ml";;

let statement =
  `let is_group =
     \(mul:G->G->G) (identity:G) (ginv:G->G).
       (!x y z:G. mul (mul x y) z = mul x (mul y z)) /\
       (!x:G. mul identity x = x /\ mul x identity = x) /\
       (!x:G.
          mul (ginv x) x = identity /\ mul x (ginv x) = identity) in
   let is_power =
     \(mul:G->G->G) (identity:G) (x:G) (n:num) (y:G).
       ?powers:num->G.
         powers 0 = identity /\
         (!k:num. powers (SUC k) = mul (powers k) x) /\
         powers n = y in
   !m n:num.
   !a:num->num.
   !mul:G->G->G identity:G ginv:G->G g h:G.
     0 < m /\
     0 < n /\
     coprime(m,n) /\
     (!k:num.
        1 <= k /\ k <= n
        ==> &(a k) =
            floor ((&m * &k) / &n) -
            floor ((&m * &(k - 1)) / &n)) /\
     is_group mul identity ginv /\
     (?hpowers products:num->G.
        products 0 = identity /\
        (!k:num.
           k < n
           ==> is_power mul identity h (a (SUC k)) (hpowers (SUC k)) /\
               products (SUC k) =
               mul (products k) (mul g (hpowers (SUC k)))) /\
        products n = identity)
     ==> mul g h = mul h g`;;
