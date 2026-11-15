(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binomial_Top_computeqtvc: a binomial-coefficient computation
  verification condition relating a multiplicative update by exact integer
  division to a recursively specified positive combination function. This
  file contains no proof.
*)

let statement =
 `!infix_sl:int->int->int.
  !comb:int->int->int.
    (!y x:int.
       ~(y = (&0:int))
       ==> infix_sl x y = x div y)
    ==>
    (!k n:int.
       (&0:int) <= k /\ k <= n
       ==>
       (if k = (&0:int) \/ k = n then
          comb n k = (&1:int)
        else
          comb n k =
            comb (n - (&1:int)) k +
            comb (n - (&1:int)) (k - (&1:int))))
    ==>
    (!k n:int.
       (&0:int) <= k /\ k <= n
       ==> (&1:int) <= comb n k)
    ==>
    !k n:int.
      (&0:int) <= k
      ==> k <= n
      ==>
      let k1 = min k (n - k) in
      (((&1:int) <= k1 + (&1:int)
        ==>
        ((((&1:int) <= (&1:int) /\
           (&1:int) <= k1 + (&1:int)) /\
          (&1:int) = comb n ((&1:int) - (&1:int))) /\
         (!r:int.
            ((!i:int.
                (((&1:int) <= i /\ i <= k1) /\
                 ((&1:int) <= i /\ i <= k1 + (&1:int)) /\
                 r = comb n (i - (&1:int)))
                ==>
                ~(i = (&0:int)) /\
                ((&1:int) <= i + (&1:int) /\
                 i + (&1:int) <= k1 + (&1:int)) /\
                infix_sl (r * (n - i + (&1:int))) i =
                  comb n (i + (&1:int) - (&1:int))) /\
             ((((&1:int) <= k1 + (&1:int) /\
                k1 + (&1:int) <= k1 + (&1:int)) /\
               r = comb n (k1 + (&1:int) - (&1:int)))
              ==> r = comb n k)))))
       /\
       (k1 + (&1:int) < (&1:int)
        ==> (&1:int) = comb n k))`;;
