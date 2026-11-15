(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_a6:
  equality of the counts of two families of positive-integer compositions,
  defined respectively by strong gap and recurrence-prefix conditions. This
  file contains no proof.
*)

let statement =
  `let nabsum =
     \n:num. \ab:num#(num->num).
       1 <= FST ab /\
       (!i:num. i < FST ab ==> 0 < SND ab i) /\
       (!i:num. FST ab <= i ==> SND ab i = 0) /\
       nsum (0..FST ab - 1) (\i. SND ab i) = n in
   let A =
     \n:num.
       CARD
         {a:num#(num->num) |
            nabsum n a /\
            (!i:num.
               i + 2 < FST a
               ==> SND a i > SND a (i + 1) + SND a (i + 2)) /\
            (1 < FST a
             ==> SND a (FST a - 2) > SND a (FST a - 1))} in
   let B =
     \g:num->num. \n:num.
       CARD
         {b:num#(num->num) |
            nabsum n b /\
            (!i:num.
               i + 1 < FST b
               ==> SND b i >= SND b (i + 1)) /\
            (!i:num.
               i < FST b
               ==> ?j:num. SND b i = g j) /\
            (?k:num.
               SND b 0 = g k /\
               (!j:num.
                  j <= k
                  ==> ?i:num. i < FST b /\ SND b i = g j))} in
   !g:num->num.
     g 0 = 1 /\
     g 1 = 2 /\
     (!j:num.
        2 <= j
        ==> g j = g (j - 1) + g (j - 2) + 1)
     ==>
     !n:num. 1 <= n ==> A n = B g n`;;
