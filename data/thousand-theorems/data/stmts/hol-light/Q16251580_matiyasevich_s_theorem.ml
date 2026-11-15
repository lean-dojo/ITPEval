(*
  Statement-only formalization of Thousand Theorems corpus artifact Q16251580,
  "Matiyasevich's theorem": Pell-sequence values are characterized by a finite
  system of natural-number equations, divisibility, and congruences. This file
  contains no proof.
*)

let q16251580_pell_pair = new_recursive_definition num_RECURSION
  `(q16251580_pell_pair a 0 = (1,0)) /\
   (!n. q16251580_pell_pair a (SUC n) =
        (FST (q16251580_pell_pair a n) * a +
           (a * a - 1) * SND (q16251580_pell_pair a n),
         FST (q16251580_pell_pair a n) +
           SND (q16251580_pell_pair a n) * a))`;;

let q16251580_pell_x = new_definition
  `q16251580_pell_x a n = FST (q16251580_pell_pair a n)`;;

let q16251580_pell_y = new_definition
  `q16251580_pell_y a n = SND (q16251580_pell_pair a n)`;;

let Q16251580_MATIYASEVIC_THEOREM =
  `!a k x y:num.
     (1 < a /\
      q16251580_pell_x a k = x /\
      q16251580_pell_y a k = y) <=>
     1 < a /\
     k <= y /\
     ((x = 1 /\ y = 0) \/
      ?u v s t b:num.
        x * x - (a * a - 1) * y * y = 1 /\
        u * u - (a * a - 1) * v * v = 1 /\
        s * s - (b * b - 1) * t * t = 1 /\
        1 < b /\
        b MOD (4 * y) = 1 MOD (4 * y) /\
        b MOD u = a MOD u /\
        0 < v /\
        (y * y) divides v /\
        s MOD u = x MOD u /\
        t MOD (4 * y) = k MOD (4 * y))`;;
