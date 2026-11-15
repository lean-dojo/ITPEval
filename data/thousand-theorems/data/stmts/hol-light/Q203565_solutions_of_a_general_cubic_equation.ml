(*
  Statement-only formalization of Thousand Theorems corpus artifact Q203565,
  "Solutions of a general cubic equation": over an arbitrary field in which
  2 and 3 are nonzero, a primitive cube root of unity and the stated auxiliary
  root data characterize exactly the three roots of a general cubic. This file
  contains no proof.
*)

let Q203565_CUBIC_EQ_ZERO_IFF =
  `let is_field =
     \(zeroA:A) (oneA:A) (add:A->A->A) (mul:A->A->A)
      (neg:A->A) (invA:A->A).
       ~(zeroA = oneA) /\
       (!u. add zeroA u = u) /\
       (!u. add (neg u) u = zeroA) /\
       (!u v. add u v = add v u) /\
       (!u v w. add u (add v w) = add (add u v) w) /\
       (!u. mul oneA u = u) /\
       (!u v. mul u v = mul v u) /\
       (!u v w. mul u (mul v w) = mul (mul u v) w) /\
       (!u v w. mul u (add v w) =
                add (mul u v) (mul u w)) /\
       invA zeroA = zeroA /\
       (!u. ~(u = zeroA) ==> mul (invA u) u = oneA) in
   !zeroA oneA:A. !add mul:A->A->A. !neg invA:A->A.
   !a b c d omega p q r s t x:A.
     let power =
       \u:A. \n:num. ITLIST mul (REPLICATE n u) oneA in
     let sub =
       \u:A. \v:A. add u (neg v) in
     let divide =
       \u:A. \v:A. mul u (invA v) in
     let two = add oneA oneA in
     let three = add two oneA in
     let nine = mul three three in
     let twentyseven = mul nine three in
     let fiftyfour = mul two twentyseven in
     let is_primitive_cube_root =
       \u:A.
         power u 3 = oneA /\
         (!n:num. power u n = oneA ==> ?k:num. n = 3 * k) in
     is_field zeroA oneA add mul neg invA /\
     ~(two = zeroA) /\
     ~(three = zeroA) /\
     ~(a = zeroA) /\
     is_primitive_cube_root omega /\
     p =
       divide
         (sub (mul (mul three a) c) (power b 2))
         (mul nine (power a 2)) /\
     ~(p = zeroA) /\
     q =
       divide
         (sub
           (sub (mul (mul (mul nine a) b) c)
                (mul two (power b 3)))
           (mul (mul twentyseven (power a 2)) d))
         (mul fiftyfour (power a 3)) /\
     power r 2 = add (power q 2) (power p 3) /\
     power s 3 = add q r /\
     mul t s = p
     ==>
     (add
        (add
          (add (mul a (power x 3)) (mul b (power x 2)))
          (mul c x))
        d = zeroA
      <=>
      x = sub (sub s t) (divide b (mul three a)) \/
      x =
        sub
          (sub (mul s omega) (mul t (power omega 2)))
          (divide b (mul three a)) \/
      x =
        sub
          (sub (mul s (power omega 2)) (mul t omega))
          (divide b (mul three a)))`;;
