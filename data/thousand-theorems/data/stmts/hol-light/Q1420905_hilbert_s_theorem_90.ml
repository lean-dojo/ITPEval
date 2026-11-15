(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1420905
  (thousand-theorems__hol-light__Q1420905), "Hilbert's theorem 90": in a
  finite cyclic Galois extension, every element of norm one is the quotient
  of a nonzero element by its image under a chosen generator of the Galois
  group. This file contains no proof.
*)

let Q1420905_HILBERT_THEOREM_90 =
  `let is_field_K =
     \(z:K) (u:K) (fadd:K->K->K) (fmul:K->K->K)
      (fneg:K->K) (finv:K->K).
       ~(z = u) /\
       (!x:K. fadd z x = x) /\
       (!x:K. fadd (fneg x) x = z) /\
       (!x y:K. fadd x y = fadd y x) /\
       (!x y z:K. fadd x (fadd y z) = fadd (fadd x y) z) /\
       (!x:K. fmul u x = x) /\
       (!x y:K. fmul x y = fmul y x) /\
       (!x y z:K. fmul x (fmul y z) = fmul (fmul x y) z) /\
       (!x y z:K. fmul x (fadd y z) =
                    fadd (fmul x y) (fmul x z)) /\
       (!x:K. ~(x = z) ==> fmul (finv x) x = u) in
   let is_field_L =
     \(z:L) (u:L) (fadd:L->L->L) (fmul:L->L->L)
      (fneg:L->L) (finv:L->L).
       ~(z = u) /\
       (!x:L. fadd z x = x) /\
       (!x:L. fadd (fneg x) x = z) /\
       (!x y:L. fadd x y = fadd y x) /\
       (!x y z:L. fadd x (fadd y z) = fadd (fadd x y) z) /\
       (!x:L. fmul u x = x) /\
       (!x y:L. fmul x y = fmul y x) /\
       (!x y z:L. fmul x (fmul y z) = fmul (fmul x y) z) /\
       (!x y z:L. fmul x (fadd y z) =
                    fadd (fmul x y) (fmul x z)) /\
       (!x:L. ~(x = z) ==> fmul (finv x) x = u) in
   let is_field_embedding =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (zeroL:L) (oneL:L) (addL:L->L->L) (mulL:L->L->L)
      (emb:K->L).
       emb zeroK = zeroL /\
       emb oneK = oneL /\
       (!a b:K. emb (addK a b) = addL (emb a) (emb b)) /\
       (!a b:K. emb (mulK a b) = mulL (emb a) (emb b)) /\
       (!a b:K. emb a = emb b ==> a = b) in
   let is_basis =
     \(n:num) (zeroK:K) (zeroL:L) (addL:L->L->L)
      (mulL:L->L->L) (emb:K->L) (b:num->L).
       (!c:num->K.
          iterate addL {i:num | i < n}
            (\i. mulL (emb (c i)) (b i)) = zeroL
          ==> !i:num. i < n ==> c i = zeroK) /\
       (!x:L.
          ?c:num->K.
            x = iterate addL {i:num | i < n}
                  (\i. mulL (emb (c i)) (b i))) in
   let is_K_automorphism =
     \(zeroL:L) (oneL:L) (addL:L->L->L) (mulL:L->L->L)
      (emb:K->L) (s:L->L).
       s zeroL = zeroL /\
       s oneL = oneL /\
       (!x y:L. s (addL x y) = addL (s x) (s y)) /\
       (!x y:L. s (mulL x y) = mulL (s x) (s y)) /\
       (!a:K. s (emb a) = emb a) /\
       (!x y:L. s x = s y ==> x = y) /\
       (!y:L. ?x:L. s x = y) in
   !zeroK oneK:K.
   !addK mulK:K->K->K.
   !negK invK:K->K.
   !zeroL oneL:L.
   !addL mulL:L->L->L.
   !negL invL:L->L.
   !emb:K->L.
     is_field_K zeroK oneK addK mulK negK invK /\
     is_field_L zeroL oneL addL mulL negL invL /\
     is_field_embedding
       zeroK oneK addK mulK zeroL oneL addL mulL emb
     ==>
     let automorphisms =
       {s:L->L |
          is_K_automorphism zeroL oneL addL mulL emb s} in
     (?n:num. ?b:num->L.
        is_basis n zeroK zeroL addL mulL emb b /\
        FINITE automorphisms /\
        CARD automorphisms = n)
     ==>
     !g:L->L.
       g IN automorphisms /\
       (!s:L->L.
          s IN automorphisms ==> ?m:num. s = ITER m g)
       ==>
       !x:L.
         iterate mulL automorphisms (\s. s x) = oneL
         ==>
         ?y:L.
           ~(y = zeroL) /\
           mulL y (invL (g y)) = x`;;
