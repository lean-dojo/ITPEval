(*
  Statement-only formalization of "Puiseux's Theorem" from Hundred Theorems
  artifact 041 (hundred-theorems__hol-light__041). Over an arbitrary
  algebraically closed field of characteristic zero, every nonconstant
  polynomial with formal Puiseux-series coefficients has a Puiseux-series
  root. This file contains no proof.
*)

let PUISEUXS_THEOREM =
  `let is_field =
       \(z0:A) (z1:A) (fld_add:A->A->A) (fld_mul:A->A->A)
        (fld_neg:A->A) (fld_inv:A->A).
          ~(z1 = z0) /\
          (!x y. fld_add x y = fld_add y x) /\
          (!x y z. fld_add (fld_add x y) z =
                   fld_add x (fld_add y z)) /\
          (!x. fld_add x z0 = x) /\
          (!x. fld_add x (fld_neg x) = z0) /\
          (!x y. fld_mul x y = fld_mul y x) /\
          (!x y z. fld_mul (fld_mul x y) z =
                   fld_mul x (fld_mul y z)) /\
          (!x. fld_mul x z1 = x) /\
          (!x y z. fld_mul x (fld_add y z) =
                   fld_add (fld_mul x y) (fld_mul x z)) /\
          (!x. ~(x = z0) ==> fld_mul x (fld_inv x) = z1) in
   let has_characteristic_zero =
       \(z0:A) (z1:A) (fld_add:A->A->A).
          !n:num. ~(n = 0)
                  ==> ~(ITLIST fld_add (REPLICATE n z1) z0 = z0) in
   let is_algebraically_closed =
       \(z0:A) (fld_add:A->A->A) (fld_mul:A->A->A).
          !p:A list.
             (?n:num. 0 < n /\ n < LENGTH p /\ ~(EL n p = z0))
             ==> ?x:A.
                    ITLIST
                      (\a acc. fld_add a (fld_mul x acc)) p z0 = z0 in
   !z0 z1:A.
   !fld_add fld_mul:A->A->A.
   !fld_neg fld_inv:A->A.
      is_field z0 z1 fld_add fld_mul fld_neg fld_inv /\
      has_characteristic_zero z0 z1 fld_add /\
      is_algebraically_closed z0 fld_add fld_mul
      ==>
      let is_puiseux =
          \(f:real->A).
             (?b:real. !q:real. q < b ==> f q = z0) /\
             (?d:num. ~(d = 0) /\
                      !q:real. ~(f q = z0)
                               ==> ?n:int. q = real_of_int n / &d) in
      let ps_zero = \q:real. z0 in
      let ps_add =
          \(f:real->A) (g:real->A) q. fld_add (f q) (g q) in
      let ps_mul =
          \(f:real->A) (g:real->A) q.
             iterate fld_add
                     {r:real | ~(f r = z0) /\
                               ~(g(q - r) = z0)}
                     (\r. fld_mul (f r) (g(q - r))) in
      !p:(real->A)list.
         (!a. MEM a p ==> is_puiseux a) /\
         (?n:num. 0 < n /\ n < LENGTH p /\ ~(EL n p = ps_zero))
         ==> ?s:real->A.
                is_puiseux s /\
                ITLIST (\a acc. ps_add a (ps_mul s acc))
                       p ps_zero =
                ps_zero`;;
