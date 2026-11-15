(*
  Statement-only formalization of miniF2F valid artifact aime_1996_p5: three
  distinct complex roots of a fixed cubic have pairwise sums that are roots of
  a second monic cubic, forcing its constant coefficient to be 23. This file
  contains no proof.
*)

needs "Complex/complexnumbers.ml";;

prioritize_complex();;

let statement = `!a:complex b:complex c:complex r:complex s:complex t:complex
                    f:complex->complex g:complex->complex.
    (!x. f x =
         x pow 3 + Cx(&3) * x pow 2 + Cx(&4) * x - Cx(&11)) /\
    (!x. g x =
         x pow 3 + r * x pow 2 + s * x + t) /\
    f a = Cx(&0) /\
    f b = Cx(&0) /\
    f c = Cx(&0) /\
    g (a + b) = Cx(&0) /\
    g (b + c) = Cx(&0) /\
    g (c + a) = Cx(&0) /\
    ~(a = b) /\
    ~(b = c) /\
    ~(c = a)
    ==> t = Cx(&23)`;;
