(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.permut_mod, catalog title "fermat.permut_mod": multiplication by a
  natural not divisible by a prime, reduced modulo that prime, maps the
  naturals through the prime's predecessor into themselves injectively.
  This file contains no proof.
*)

let statement =
  `!p a:num.
     prime p
     ==> ~(p divides a)
     ==> ((!i:num.
             i <= p - 1
             ==> (a * i) MOD p <= p - 1) /\
          (!i j:num.
             i <= p - 1
             ==> j <= p - 1
             ==> (a * i) MOD p = (a * j) MOD p
             ==> i = j))`;;
