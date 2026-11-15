(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_a2
  (putnambench__hol-light__putnam_2017_a2): integer polynomiality of the
  positive-index terms in the stated rational-function recurrence.
  This file contains no proof.
*)

let statement =
  `let eval =
     \p:real list. \x:real.
       ITLIST (\c acc. c + x * acc) p (&0) in
   let eval_int =
     \p:int list. \x:real.
       ITLIST (\c acc. real_of_int c + x * acc) p (&0) in
   let is_rational =
     \x:real.
       ?a:int. ?b:num.
         ~(b = 0) /\ x = real_of_int a / &b in
   let rational_poly =
     \p:real list. !c:real. MEM c p ==> is_rational c in
   let valid =
     \q:(real list)#(real list).
       rational_poly (FST q) /\
       rational_poly (SND q) /\
       ~(!x:real. eval (SND q) x = &0) in
   let rat_eq =
     \q:(real list)#(real list).
     \r:(real list)#(real list).
       !x:real.
         eval (FST q) x * eval (SND r) x =
         eval (FST r) x * eval (SND q) x in
   let rat_zero =
     \q:(real list)#(real list).
       !x:real. eval (FST q) x = &0 in
   let recurrence =
     \qprev:(real list)#(real list).
     \qcur:(real list)#(real list).
     \qnext:(real list)#(real list).
       if rat_zero qprev
       then rat_eq qnext ([&0],[&1])
       else
         !x:real.
           eval (FST qnext) x *
           ((eval (SND qcur) x) pow 2 * eval (FST qprev) x) =
           (((eval (FST qcur) x) pow 2 -
             (eval (SND qcur) x) pow 2) *
            eval (SND qprev) x) *
           eval (SND qnext) x in
   !Q:num->(real list)#(real list).
     (!n:num. valid (Q n)) /\
     rat_eq (Q 0) ([&1],[&1]) /\
     rat_eq (Q 1) ([&0; &1],[&1]) /\
     (!n:num. recurrence (Q n) (Q (n + 1)) (Q (n + 2)))
     ==>
     !n:num.
       0 < n
       ==> ?p:int list.
             !x:real.
               eval (FST (Q n)) x =
               eval_int p x * eval (SND (Q n)) x`;;
