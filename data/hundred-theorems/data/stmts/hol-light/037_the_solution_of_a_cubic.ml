(* ========================================================================= *)
(* Cubic formula.                                                            *)
(* ========================================================================= *)

needs "Complex/complex_transc.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Define cube roots (it doesn't matter which one we choose here)            *)
(* ------------------------------------------------------------------------- *)

let ccbrt = new_definition
 `ccbrt(z) = if z = Cx(&0) then Cx(&0) else cexp(clog(z) / Cx(&3))`;;

let CCBRT = `!z. ccbrt(z) pow 3 = z`;;

(* ------------------------------------------------------------------------- *)
(* The reduction to a simpler form.                                          *)
(* ------------------------------------------------------------------------- *)

let CUBIC_REDUCTION = COMPLEX_FIELD
  `~(a = Cx(&0)) /\
   x = y - b / (Cx(&3) * a) /\
   p = (Cx(&3) * a * c - b pow 2) / (Cx(&9) * a pow 2) /\
   q = (Cx(&9) * a * b * c - Cx(&2) * b pow 3 - Cx(&27) * a pow 2 * d) /
       (Cx(&54) * a pow 3)
   ==> (a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
        y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0))`;;

(* ------------------------------------------------------------------------- *)
(* The solutions of the special form.                                        *)
(* ------------------------------------------------------------------------- *)

let CUBIC_BASIC = COMPLEX_FIELD
 `!i t s.
    s pow 2 = q pow 2 + p pow 3 /\
    (s1 pow 3 = if p = Cx(&0) then Cx(&2) * q else q + s) /\
    s2 = --s1 * (Cx(&1) + i * t) / Cx(&2) /\
    s3 = --s1 * (Cx(&1) - i * t) / Cx(&2) /\
    i pow 2 + Cx(&1) = Cx(&0) /\
    t pow 2 = Cx(&3)
    ==> if p = Cx(&0) then
          (y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0) <=>
           y = s1 \/ y = s2 \/ y = s3)
        else
          ~(s1 = Cx(&0)) /\
          (y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0) <=>
               (y = s1 - p / s1 \/ y = s2 - p / s2 \/ y = s3 - p / s3))`;;

(* ------------------------------------------------------------------------- *)
(* Explicit formula for the roots (doesn't matter which square/cube roots).  *)
(* ------------------------------------------------------------------------- *)

let CUBIC = `~(a = Cx(&0))
   ==> let p = (Cx(&3) * a * c - b pow 2) / (Cx(&9) * a pow 2)
       and q = (Cx(&9) * a * b * c - Cx(&2) * b pow 3 - Cx(&27) * a pow 2 * d) /
               (Cx(&54) * a pow 3) in
       let s = csqrt(q pow 2 + p pow 3) in
       let s1 = if p = Cx(&0) then ccbrt(Cx(&2) * q) else ccbrt(q + s) in
       let s2 = --s1 * (Cx(&1) + ii * csqrt(Cx(&3))) / Cx(&2)
       and s3 = --s1 * (Cx(&1) - ii * csqrt(Cx(&3))) / Cx(&2) in
       if p = Cx(&0) then
         a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
            x = s1 - b / (Cx(&3) * a) \/
            x = s2 - b / (Cx(&3) * a) \/
            x = s3 - b / (Cx(&3) * a)
       else
         ~(s1 = Cx(&0)) /\
         (a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
             x = s1 - p / s1 - b / (Cx(&3) * a) \/
             x = s2 - p / s2 - b / (Cx(&3) * a) \/
             x = s3 - p / s3 - b / (Cx(&3) * a))`;;
