(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/gcd_vc_sp_BinaryGcd_binary_gcdqtvc: the binary-GCD verification
  condition for recursive-call descent and preservation of the integer
  greatest common divisor. This file contains no proof.
*)

let statement =
  `!u v:int.
     (&0:int) <= u
     ==>
     (&0:int) <= v
     ==>
     ((if u < v then
         (((&0:int) <= v /\ u < v) \/
          (v = u /\ (&0:int) <= u /\ v < u)) /\
         (&0:int) <= v /\
         (&0:int) <= u
       else
         ~(v = (&0:int))
         ==>
         ~((&2:int) = (&0:int)) /\
         (if u rem (&2:int) = (&0:int) then
            ~((&2:int) = (&0:int)) /\
            (if v rem (&2:int) = (&0:int) then
               ~((&2:int) = (&0:int)) /\
               (let o1 = v div (&2:int) in
                ~((&2:int) = (&0:int)) /\
                (let o2 = u div (&2:int) in
                 (((&0:int) <= v /\ o1 < v) \/
                  (v = o1 /\ (&0:int) <= u /\ o2 < u)) /\
                 (&0:int) <= o2 /\
                 (&0:int) <= o1))
             else
               ~((&2:int) = (&0:int)) /\
               (let o1 = u div (&2:int) in
                ((&0:int) <= u /\ o1 < u) /\
                (&0:int) <= o1 /\
                (&0:int) <= v))
          else
            ~((&2:int) = (&0:int)) /\
            (if v rem (&2:int) = (&0:int) then
               ~((&2:int) = (&0:int)) /\
               (let o1 = v div (&2:int) in
                ((&0:int) <= v /\ o1 < v) /\
                (&0:int) <= u /\
                (&0:int) <= o1)
             else
               ~((&2:int) = (&0:int)) /\
               (let o1 = (u - v) div (&2:int) in
                ((&0:int) <= u /\ o1 < u) /\
                (&0:int) <= o1 /\
                (&0:int) <= v)))) /\
      (!result:int.
         (if u < v then
            result = gcd(v,u)
          else if v = (&0:int) then
            result = u
          else if u rem (&2:int) = (&0:int) then
            if v rem (&2:int) = (&0:int) then
              result =
                (&2:int) *
                gcd(u div (&2:int),v div (&2:int))
            else
              result = gcd(u div (&2:int),v)
          else if v rem (&2:int) = (&0:int) then
            result = gcd(u,v div (&2:int))
          else
            result = gcd((u - v) div (&2:int),v))
         ==>
         result = gcd(u,v)))`;;
