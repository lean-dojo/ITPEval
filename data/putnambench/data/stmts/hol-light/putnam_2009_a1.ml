(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_a1:
  the zero-sum condition on the values of a real function at the vertices of
  every nondegenerate square forces the function to vanish on the plane; the
  answer is affirmative. This file contains no proof.
*)

let statement =
  `((!f:(real#real)->real.
       (!O v:real#real.
          ~(v = (&0,&0))
          ==>
          f O +
          f (FST O + FST v,SND O + SND v) +
          f (FST O + FST v - SND v,SND O + SND v + FST v) +
          f (FST O - SND v,SND O + FST v) = &0)
       ==>
       !P:real#real. f P = &0)
    <=> T)`;;
