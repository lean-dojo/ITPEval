(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b5
  (putnambench__hol-light__putnam_2022_b5): the zero value has maximal
  probability for every finite integer linear combination of independent
  {-1,0,1}-valued variables exactly when p lies in [0,1/4]. This file
  contains no proof.
*)

let statement =
  `!p:real.
   !Xset:num->int list->bool.
   !Xprob:num->int list->real.
   !P:num->int->int list->real.
     (!n:num.
        0 < n
        ==> Xset n =
            {X:int list |
               LENGTH X = n /\
               (!i:num.
                  i < n
                  ==> EL i X = (&1:int) \/
                      EL i X = --(&1:int) \/
                      EL i X = (&0:int))}) /\
     (!n:num. !X:int list.
        0 < n /\ LENGTH X = n
        ==> Xprob n X =
            product (0..n - 1)
              (\i:num.
                 if EL i X = (&1:int) \/ EL i X = --(&1:int)
                 then p
                 else &1 - &2 * p)) /\
     (!n:num. !b:int. !a:int list.
        0 < n /\ LENGTH a = n
        ==> P n b a =
            sum
              {X:int list |
                 X IN Xset n /\
                 isum (0..n - 1)
                   (\i:num. EL i a * EL i X) = b}
              (\X:int list. Xprob n X))
     ==>
     ((&0 <= p /\
       p <= &1 / &2 /\
       (!n:num. !b:int. !a:int list.
          0 < n /\ LENGTH a = n
          ==> P n (&0:int) a >= P n b a))
      <=>
      (&0 <= p /\ p <= &1 / &4))`;;
