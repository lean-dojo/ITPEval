(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_b5:
  disproof of the proposed classification of polynomial substitutions preserving
  x^2 + y^2 + z^2 + xyz. This file contains no proof.
*)

let statement =
  `let polynomial =
     \p:(num#num#num)->real. FINITE {m | ~(p m = &0)} in
   let peval =
     \p:(num#num#num)->real. \x y z:real.
       sum {m | ~(p m = &0)}
         (\m.
            p m *
            x pow (FST m) *
            y pow (FST (SND m)) *
            z pow (SND (SND m))) in
   let xpoly =
     \m:num#num#num. if m = (1,0,0) then &1 else &0 in
   let ypoly =
     \m:num#num#num. if m = (0,1,0) then &1 else &0 in
   let zpoly =
     \m:num#num#num. if m = (0,0,1) then &1 else &0 in
   let negp =
     \p:(num#num#num)->real. \m:num#num#num. --(p m) in
   let f =
     \x y z:real. x pow 2 + y pow 2 + z pow 2 + x * y * z in
   let allowed =
     \p:(num#num#num)->real.
      \q:(num#num#num)->real.
       \r:(num#num#num)->real.
        p INSERT q INSERT r INSERT {} =
          xpoly INSERT ypoly INSERT zpoly INSERT {} \/
        p INSERT q INSERT r INSERT {} =
          xpoly INSERT negp ypoly INSERT negp zpoly INSERT {} \/
        p INSERT q INSERT r INSERT {} =
          negp xpoly INSERT ypoly INSERT negp zpoly INSERT {} \/
        p INSERT q INSERT r INSERT {} =
          negp xpoly INSERT negp ypoly INSERT zpoly INSERT {} in
   ((!p:(num#num#num)->real.
      !q:(num#num#num)->real.
      !r:(num#num#num)->real.
       polynomial p /\
       polynomial q /\
       polynomial r /\
       (!x y z:real.
          f (peval p x y z) (peval q x y z) (peval r x y z) =
          f x y z)
       ==> allowed p q r) <=>
    F)`;;
