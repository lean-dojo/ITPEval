(*
  Statement-only formalization of Thousand Theorems corpus artifact Q476776,
  "Solutions of a general quartic equation": over an arbitrary field in which
  2 is invertible, the stated cubic-resolvent and square-root data characterize
  exactly the four roots of a general quartic. This file contains no proof.
*)

let Q476776_QUARTIC_EQ_ZERO_IFF =
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
   !a b c d e p q r s u v w x:A.
     let power =
       \z:A. \n:num. ITLIST mul (REPLICATE n z) oneA in
     let sub =
       \z:A. \y:A. add z (neg y) in
     let divide =
       \z:A. \y:A. mul z (invA y) in
     let two = add oneA oneA in
     let three = add two oneA in
     let four = mul two two in
     let eight = mul four two in
     let sixteen = mul four four in
     let sixtyfour = mul eight eight in
     let twohundredfiftysix = mul sixteen sixteen in
     is_field zeroA oneA add mul neg invA /\
     ~(two = zeroA) /\
     ~(a = zeroA) /\
     p =
       divide
         (sub
           (mul (mul eight a) c)
           (mul three (power b 2)))
         (mul eight (power a 2)) /\
     q =
       divide
         (add
           (sub
             (power b 3)
             (mul (mul (mul four a) b) c))
           (mul (mul eight (power a 2)) d))
         (mul eight (power a 3)) /\
     ~(q = zeroA) /\
     r =
       divide
         (sub
           (sub
             (add
               (mul (mul (mul sixteen a) (power b 2)) c)
               (mul (mul twohundredfiftysix (power a 3)) e))
             (mul three (power b 4)))
           (mul (mul (mul sixtyfour (power a 2)) b) d))
         (mul twohundredfiftysix (power a 4)) /\
     sub
       (add
         (sub
           (sub
             (power u 3)
             (mul p (power u 2)))
           (mul (mul four r) u))
         (mul (mul four p) r))
       (power q 2) = zeroA /\
     power s 2 = sub u p /\
     power v 2 =
       sub
         (mul four (power s 2))
         (mul eight (sub u (divide q s))) /\
     power w 2 =
       sub
         (mul four (power s 2))
         (mul eight (add u (divide q s)))
     ==>
     (add
        (add
          (add
            (add
              (mul a (power x 4))
              (mul b (power x 3)))
            (mul c (power x 2)))
          (mul d x))
        e = zeroA
      <=>
      x =
        sub
          (divide
            (sub (neg (mul two s)) v)
            four)
          (divide b (mul four a)) \/
      x =
        sub
          (divide
            (add (neg (mul two s)) v)
            four)
          (divide b (mul four a)) \/
      x =
        sub
          (divide
            (sub (mul two s) w)
            four)
          (divide b (mul four a)) \/
      x =
        sub
          (divide
            (add (mul two s) w)
            four)
          (divide b (mul four a)))`;;
