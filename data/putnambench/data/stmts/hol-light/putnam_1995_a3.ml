(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a3:
  nine decimal digit replacements divisible by seven in two successive steps
  force each original-to-final digit difference to be divisible by seven.
  This file contains no proof.
*)

let statement =
  `!relation:(num->int)->(num->int)->bool.
   !digits_to_num:(num->int)->int.
     digits_to_num =
       (\dig:num->int.
          isum (0..8) (\i. dig i * ((&10:int) pow i))) /\
     (!d e:num->int.
        relation d e <=>
        ((!i:num.
            i < 9
            ==> d i < &10 /\ &0 <= d i /\
                e i < &10 /\ &0 <= e i) /\
         (!i:num.
            i < 9
            ==> (&7:int) divides
                digits_to_num
                  (\j:num. if j = i then e j else d j))))
     ==> !d e f:num->int.
           relation d e /\ relation e f
           ==> (!i:num. i < 9 ==> (&7:int) divides (d i - f i))`;;
