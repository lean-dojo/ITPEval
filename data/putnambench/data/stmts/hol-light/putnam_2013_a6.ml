(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_a6:
  positivity of the prescribed integer-weight double sum over every finite
  nonempty subset of the integer lattice. This file contains no proof.
*)

let statement =
  `!w:int->int->int. !A:((int#int)->bool)->int.
     w (--(&2:int)) (--(&2:int)) = --(&1:int) /\
     w (&2:int) (--(&2:int)) = --(&1:int) /\
     w (--(&2:int)) (&2:int) = --(&1:int) /\
     w (&2:int) (&2:int) = --(&1:int) /\
     w (--(&1:int)) (--(&2:int)) = --(&2:int) /\
     w (&1:int) (--(&2:int)) = --(&2:int) /\
     w (--(&2:int)) (--(&1:int)) = --(&2:int) /\
     w (&2:int) (--(&1:int)) = --(&2:int) /\
     w (--(&2:int)) (&1:int) = --(&2:int) /\
     w (&2:int) (&1:int) = --(&2:int) /\
     w (--(&1:int)) (&2:int) = --(&2:int) /\
     w (&1:int) (&2:int) = --(&2:int) /\
     w (&0:int) (--(&2:int)) = (&2:int) /\
     w (--(&2:int)) (&0:int) = (&2:int) /\
     w (&2:int) (&0:int) = (&2:int) /\
     w (&0:int) (&2:int) = (&2:int) /\
     w (--(&1:int)) (--(&1:int)) = (&4:int) /\
     w (&1:int) (--(&1:int)) = (&4:int) /\
     w (--(&1:int)) (&1:int) = (&4:int) /\
     w (&1:int) (&1:int) = (&4:int) /\
     w (&0:int) (--(&1:int)) = --(&4:int) /\
     w (--(&1:int)) (&0:int) = --(&4:int) /\
     w (&1:int) (&0:int) = --(&4:int) /\
     w (&0:int) (&1:int) = --(&4:int) /\
     w (&0:int) (&0:int) = (&12:int) /\
     (!a b:int.
        abs a > (&2:int) \/ abs b > (&2:int)
        ==> w a b = (&0:int)) /\
     (!S:(int#int)->bool.
        FINITE S
        ==> A S =
            isum S
              (\s:int#int.
                 isum S
                   (\t:int#int.
                      w (FST s - FST t) (SND s - SND t))))
     ==>
     !S:(int#int)->bool.
       FINITE S /\ ~(S = {})
       ==> A S > (&0:int)`;;
