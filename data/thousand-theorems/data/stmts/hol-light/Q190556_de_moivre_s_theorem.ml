(*
  Statement-only formalization of Thousand Theorems corpus artifact Q190556,
  "De Moivre's theorem": every natural power of cos(z) + sin(z)i equals
  cos(nz) + sin(nz)i for standard complex sine and cosine defined from the
  power-series exponential. This file contains no proof.
*)

let Q190556_DE_MOIVRE_S_THEOREM =
  `let czero = ((&0:real),(&0:real)) in
   let cone = ((&1:real),(&0:real)) in
   let ci = ((&0:real),(&1:real)) in
   let cneg =
     \(z:real#real). (--(FST z),--(SND z)) in
   let cadd =
     \(z:real#real) (w:real#real).
       (FST z + FST w,SND z + SND w) in
   let csub =
     \(z:real#real) (w:real#real).
       cadd z (cneg w) in
   let cmul =
     \(z:real#real) (w:real#real).
       (FST z * FST w - SND z * SND w,
        FST z * SND w + SND z * FST w) in
   let cscale =
     \(a:real) (z:real#real).
       (a * FST z,a * SND z) in
   let cnorm =
     \(z:real#real).
       sqrt(FST z * FST z + SND z * SND z) in
   let cpow =
     \(z:real#real) (n:num).
       @w:real#real.
         ?p:num->real#real.
           p 0 = cone /\
           (!m:num. p (SUC m) = cmul z (p m)) /\
           p n = w in
   let cexp =
     \(z:real#real).
       @w:real#real.
         ?s:num->real#real.
           s 0 = czero /\
           (!m:num.
              s (SUC m) =
              cadd (s m)
                (cscale (inv(&(FACT m))) (cpow z m))) /\
           (!epsilon:real.
              &0 < epsilon
              ==> ?N:num. !m:num.
                    N <= m
                    ==> cnorm (csub (s m) w) < epsilon) in
   let ccos =
     \(z:real#real).
       cscale (inv(&2))
         (cadd (cexp (cmul z ci))
               (cexp (cneg (cmul z ci)))) in
   let csin =
     \(z:real#real).
       cscale (inv(&2))
         (cmul
           (csub (cexp (cneg (cmul z ci)))
                 (cexp (cmul z ci)))
           ci) in
   !n:num. !z:real#real.
     cpow (cadd (ccos z) (cmul (csin z) ci)) n =
     cadd (ccos (cscale (&n) z))
          (cmul (csin (cscale (&n) z)) ci)`;;
