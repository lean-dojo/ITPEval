(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_b6:
  modulo a prime, the determinant of the three-variable Frobenius-power
  matrix is coefficientwise congruent to a finite product of integer linear
  forms. This file contains no proof.
*)

let statement =
  `let pmul =
     \f g:(num#num#num)->int.
      \(i,j,k):num#num#num.
       isum (0..i)
         (\a:num.
            isum (0..j)
              (\b:num.
                 isum (0..k)
                   (\c:num.
                      f (a,b,c) * g (i - a,j - b,k - c)))) in
   let padd =
     \f g:(num#num#num)->int.
      \m:num#num#num. f m + g m in
   let psub =
     \f g:(num#num#num)->int.
      \m:num#num#num. f m - g m in
   let pone =
     \m:num#num#num. if m = (0,0,0) then &1 else &0 in
   let monomial =
     \e:num#num#num.
      \m:num#num#num. if m = e then &1 else &0 in
   let linear =
     \(a,b,c):int#int#int.
      \m:num#num#num.
       if m = (1,0,0) then a
       else if m = (0,1,0) then b
       else if m = (0,0,1) then c
       else &0 in
   let detpoly =
     \p:num.
       psub
         (padd
           (padd
             (pmul (monomial (1,0,0))
               (pmul (monomial (0,p,0))
                     (monomial (0,0,p EXP 2))))
             (pmul (monomial (0,1,0))
               (pmul (monomial (0,0,p))
                     (monomial (p EXP 2,0,0)))))
           (pmul (monomial (0,0,1))
             (pmul (monomial (p,0,0))
                   (monomial (0,p EXP 2,0)))))
         (padd
           (padd
             (pmul (monomial (0,0,1))
               (pmul (monomial (0,p,0))
                     (monomial (p EXP 2,0,0))))
             (pmul (monomial (0,1,0))
               (pmul (monomial (p,0,0))
                     (monomial (0,0,p EXP 2)))))
           (pmul (monomial (1,0,0))
             (pmul (monomial (0,0,p))
                   (monomial (0,p EXP 2,0))))) in
   !p:num.
     prime p
     ==>
     ?L:(int#int#int)list.
       !m:num#num#num.
         (detpoly p m ==
          ITLIST (\abc acc. pmul (linear abc) acc) L pone m)
         (mod (&p:int))`;;
