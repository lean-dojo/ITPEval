(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binary_search_Complexity_binary_searchqtvc: a binary-search
  verification condition combining sorted integer-list bounds, exclusion of
  the target outside the active interval, interval decrease, and a logarithmic
  time bound. This file contains no proof.
*)

let statement =
 `let cdiv =
    \(n:int) (d:int).
      if (&0:int) <= n
      then if (&0:int) <= d then n div d else --(n div --d)
      else if (&0:int) <= d then --(--n div d) else --n div --d in
  let nth_i =
    \(a:int list) (i:int).
      if i < (&0:int) then
        if a = [] then (&0:int) else EL 0 a
      else if num_of_int i < LENGTH a then EL (num_of_int i) a
      else (&0:int) in
  !log2:int->int.
    (!n:int.
       if n <= (&1:int) then
         log2 n = (&0:int)
       else
         log2 n = (&1:int) + log2 (cdiv n (&2:int)))
    ==>
    let f =
      \n:int.
        if n = (&0:int) then (&0:int)
        else (&1:int) + log2 n in
    !a:int list. !v:int.
      (!i1 i2:int.
         (&0:int) <= i1 /\ i1 <= i2 /\
         i2 < &(LENGTH a)
         ==> nth_i a i1 <= nth_i a i2)
      ==>
      let o1 = &(LENGTH a) in
      (((&0:int) <= (&0:int) /\
        (&0:int) <= o1 /\
        o1 <= &(LENGTH a)) /\
       (!i:int.
          ((&0:int) <= i /\ i < (&0:int)) \/
          (o1 <= i /\ i < &(LENGTH a))
          ==> ~(nth_i a i = v)) /\
       (&0:int) - (&0:int) + f (o1 - (&0:int)) <=
         f (&(LENGTH a))) /\
      (!hi lo time:int.
         ((&0:int) <= lo /\ lo <= hi /\ hi <= &(LENGTH a)) /\
         (!i:int.
            ((&0:int) <= i /\ i < lo) \/
            (hi <= i /\ i < &(LENGTH a))
            ==> ~(nth_i a i = v)) /\
         time - (&0:int) + f (hi - lo) <= f (&(LENGTH a))
         ==>
         if lo < hi then
           ~((&2:int) = (&0:int)) /\
           (let mid = lo + cdiv (hi - lo) (&2:int) in
            ((&0:int) <= mid /\ mid < &(LENGTH a)) /\
            (if nth_i a mid < v then
               ((&0:int) <= hi - lo /\
                hi - (mid + (&1:int)) < hi - lo) /\
               ((&0:int) <= mid + (&1:int) /\
                mid + (&1:int) <= hi /\
                hi <= &(LENGTH a)) /\
               (!i:int.
                  ((&0:int) <= i /\ i < mid + (&1:int)) \/
                  (hi <= i /\ i < &(LENGTH a))
                  ==> ~(nth_i a i = v)) /\
               time + (&1:int) - (&0:int) +
                 f (hi - (mid + (&1:int))) <= f (&(LENGTH a))
             else
               ((&0:int) <= mid /\ mid < &(LENGTH a)) /\
               (if v < nth_i a mid then
                  ((&0:int) <= hi - lo /\ mid - lo < hi - lo) /\
                  ((&0:int) <= lo /\ lo <= mid /\
                   mid <= &(LENGTH a)) /\
                  (!i:int.
                     ((&0:int) <= i /\ i < lo) \/
                     (mid <= i /\ i < &(LENGTH a))
                     ==> ~(nth_i a i = v)) /\
                  time + (&1:int) - (&0:int) + f (mid - lo) <=
                    f (&(LENGTH a))
                else
                  (((( &0:int) <= mid /\ mid < &(LENGTH a)) /\
                    nth_i a mid = v) \/
                   (mid = --(&1:int) /\
                    (!i:int.
                       (&0:int) <= i /\ i < &(LENGTH a)
                       ==> ~(nth_i a i = v)))) /\
                  time - (&0:int) <= f (&(LENGTH a)))))
         else
           (((((&0:int) <= --(&1:int) /\
               --(&1:int) < &(LENGTH a)) /\
              nth_i a (--(&1:int)) = v) \/
             (!i:int.
                (&0:int) <= i /\ i < &(LENGTH a)
                ==> ~(nth_i a i = v))) /\
            time - (&0:int) <= f (&(LENGTH a))))`;;
