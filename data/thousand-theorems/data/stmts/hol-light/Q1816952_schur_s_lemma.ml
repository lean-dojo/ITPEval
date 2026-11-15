(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1816952,
  "Schur's lemma": over an algebraically closed field, the finite-dimensional
  endomorphism space of a simple object in a linear preadditive category with
  kernels has dimension one. This file contains no proof.
*)

let Q1816952_SCHUR_S_LEMMA =
  `let arrow =
     \(objects:O->bool) (hom:O->O->M->bool) (x:O) (y:O) (f:M).
       objects x /\ objects y /\ hom x y f in
   let is_field =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (negK:K->K) (invK:K->K).
       ~(zeroK = oneK) /\
       (!a:K. addK zeroK a = a) /\
       (!a:K. addK (negK a) a = zeroK) /\
       (!a b:K. addK a b = addK b a) /\
       (!a b c:K. addK a (addK b c) = addK (addK a b) c) /\
       (!a:K. mulK oneK a = a) /\
       (!a b:K. mulK a b = mulK b a) /\
       (!a b c:K. mulK a (mulK b c) = mulK (mulK a b) c) /\
       (!a b c:K.
          mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
       invK zeroK = zeroK /\
       (!a:K. ~(a = zeroK) ==> mulK (invK a) a = oneK) in
   let power =
     \(oneK:K) (mulK:K->K->K) (a:K) (n:num).
       ITLIST mulK (REPLICATE n a) oneK in
   let is_polynomial =
     \(zeroK:K) (p:num->K). FINITE {n | ~(p n = zeroK)} in
   let polynomial_eval =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (p:num->K) (a:K).
       iterate addK {n | ~(p n = zeroK)}
         (\n. mulK (p n) (power oneK mulK a n)) in
   let is_algebraically_closed =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K).
       !p:num->K.
         is_polynomial zeroK p /\
         (?n:num. ~(n = 0) /\ ~(p n = zeroK))
         ==> ?a:K. polynomial_eval zeroK oneK addK mulK p a = zeroK in
   let is_category =
     \(objects:O->bool) (hom:O->O->M->bool)
      (identity:O->M) (compose:M->M->M).
       (!x y x' y':O. !f:M.
          arrow objects hom x y f /\
          arrow objects hom x' y' f
          ==> x = x' /\ y = y') /\
       (!x:O.
          objects x
          ==> arrow objects hom x x (identity x)) /\
       (!x y z:O. !f g:M.
          arrow objects hom x y f /\
          arrow objects hom y z g
          ==> arrow objects hom x z (compose g f)) /\
       (!x y:O. !f:M.
          arrow objects hom x y f
          ==> compose (identity y) f = f /\
              compose f (identity x) = f) /\
       (!w x y z:O. !f g h:M.
          arrow objects hom w x f /\
          arrow objects hom x y g /\
          arrow objects hom y z h
          ==> compose h (compose g f) = compose (compose h g) f) in
   let is_preadditive =
     \(objects:O->bool) (hom:O->O->M->bool)
      (identity:O->M) (compose:M->M->M)
      (zero:O->O->M) (add:O->O->M->M->M) (neg:O->O->M->M).
       is_category objects hom identity compose /\
       (!x y:O.
          objects x /\ objects y
          ==> arrow objects hom x y (zero x y)) /\
       (!x y:O. !f g:M.
          arrow objects hom x y f /\
          arrow objects hom x y g
          ==> arrow objects hom x y (add x y f g)) /\
       (!x y:O. !f:M.
          arrow objects hom x y f
          ==> arrow objects hom x y (neg x y f)) /\
       (!x y:O. !f:M.
          arrow objects hom x y f
          ==> add x y (zero x y) f = f /\
              add x y (neg x y f) f = zero x y) /\
       (!x y:O. !f g:M.
          arrow objects hom x y f /\
          arrow objects hom x y g
          ==> add x y f g = add x y g f) /\
       (!x y:O. !f g h:M.
          arrow objects hom x y f /\
          arrow objects hom x y g /\
          arrow objects hom x y h
          ==> add x y f (add x y g h) =
              add x y (add x y f g) h) /\
       (!w x y:O. !f g h:M.
          arrow objects hom w x f /\
          arrow objects hom w x g /\
          arrow objects hom x y h
          ==> compose h (add w x f g) =
              add w y (compose h f) (compose h g)) /\
       (!w x y:O. !f g h:M.
          arrow objects hom w x f /\
          arrow objects hom x y g /\
          arrow objects hom x y h
          ==> compose (add x y g h) f =
              add w y (compose g f) (compose h f)) in
   let is_linear =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (objects:O->bool) (hom:O->O->M->bool)
      (compose:M->M->M) (zero:O->O->M)
      (add:O->O->M->M->M) (smul:O->O->K->M->M).
       (!x y:O. !a:K. !f:M.
          arrow objects hom x y f
          ==> arrow objects hom x y (smul x y a f)) /\
       (!x y:O. !f:M.
          arrow objects hom x y f
          ==> smul x y oneK f = f) /\
       (!x y:O. !a b:K. !f:M.
          arrow objects hom x y f
          ==> smul x y (mulK a b) f =
              smul x y a (smul x y b f)) /\
       (!x y:O. !a b:K. !f:M.
          arrow objects hom x y f
          ==> smul x y (addK a b) f =
              add x y (smul x y a f) (smul x y b f)) /\
       (!x y:O. !a:K. !f g:M.
          arrow objects hom x y f /\
          arrow objects hom x y g
          ==> smul x y a (add x y f g) =
              add x y (smul x y a f) (smul x y a g)) /\
       (!x y:O. !f:M.
          arrow objects hom x y f
          ==> smul x y zeroK f = zero x y) /\
       (!x y:O. !a:K.
          objects x /\ objects y
          ==> smul x y a (zero x y) = zero x y) /\
       (!w x y:O. !a:K. !f g:M.
          arrow objects hom w x f /\
          arrow objects hom x y g
          ==> compose g (smul w x a f) =
              smul w y a (compose g f) /\
              compose (smul x y a g) f =
              smul w y a (compose g f)) in
   let is_monic =
     \(objects:O->bool) (hom:O->O->M->bool)
      (compose:M->M->M) (x:O) (y:O) (f:M).
       arrow objects hom x y f /\
       !z:O. !g h:M.
         arrow objects hom z x g /\
         arrow objects hom z x h /\
         compose f g = compose f h
         ==> g = h in
   let is_isomorphism =
     \(objects:O->bool) (hom:O->O->M->bool)
      (identity:O->M) (compose:M->M->M)
      (x:O) (y:O) (f:M).
       arrow objects hom x y f /\
       ?g:M.
         arrow objects hom y x g /\
         compose g f = identity x /\
         compose f g = identity y in
   let is_simple =
     \(objects:O->bool) (hom:O->O->M->bool)
      (identity:O->M) (compose:M->M->M) (zero:O->O->M) (x:O).
       objects x /\
       ~(identity x = zero x x) /\
       !y:O. !f:M.
         is_monic objects hom compose y x f
         ==> f = zero y x \/
             is_isomorphism objects hom identity compose y x f in
   let is_kernel =
     \(objects:O->bool) (hom:O->O->M->bool)
      (compose:M->M->M) (zero:O->O->M)
      (kobject:O) (x:O) (y:O) (k:M) (f:M).
       arrow objects hom kobject x k /\
       arrow objects hom x y f /\
       compose f k = zero kobject y /\
       !z:O. !g:M.
         arrow objects hom z x g /\
         compose f g = zero z y
         ==> ?u:M.
               arrow objects hom z kobject u /\
               compose k u = g /\
               !v:M.
                 arrow objects hom z kobject v /\
                 compose k v = g
                 ==> v = u in
   let has_kernels =
     \(objects:O->bool) (hom:O->O->M->bool)
      (compose:M->M->M) (zero:O->O->M).
       !x y:O. !f:M.
         arrow objects hom x y f
         ==> ?kobject:O. ?k:M.
               objects kobject /\
               is_kernel objects hom compose zero kobject x y k f in
   let linear_combination =
     \(zero:O->O->M) (add:O->O->M->M->M)
      (smul:O->O->K->M->M) (x:O) (y:O)
      (n:num) (basis:num->M) (coeff:num->K) (v:M).
       ?partial:num->M.
         partial 0 = zero x y /\
         (!i:num.
            i < n
            ==> partial (SUC i) =
                add x y (partial i) (smul x y (coeff i) (basis i))) /\
         partial n = v in
   let has_dimension =
     \(objects:O->bool) (hom:O->O->M->bool)
      (zero:O->O->M) (add:O->O->M->M->M)
      (smul:O->O->K->M->M) (x:O) (y:O)
      (n:num) (basis:num->M).
       objects x /\ objects y /\
       (!i:num. i < n ==> arrow objects hom x y (basis i)) /\
       (!v:M.
          arrow objects hom x y v
          ==> ?coeff:num->K.
                linear_combination zero add smul x y n basis coeff v) /\
       (!v:M. !c d:num->K.
          arrow objects hom x y v /\
          linear_combination zero add smul x y n basis c v /\
          linear_combination zero add smul x y n basis d v
          ==> !i:num. i < n ==> c i = d i) in
   let finite_dimensional =
     \(objects:O->bool) (hom:O->O->M->bool)
      (zero:O->O->M) (add:O->O->M->M->M)
      (smul:O->O->K->M->M) (x:O) (y:O).
       ?n:num. ?basis:num->M.
         has_dimension objects hom zero add smul x y n basis in
   !zeroK oneK:K.
   !addK mulK:K->K->K.
   !negK invK:K->K.
   !objects:O->bool.
   !hom:O->O->M->bool.
   !identity:O->M.
   !compose:M->M->M.
   !zero:O->O->M.
   !add:O->O->M->M->M.
   !neg:O->O->M->M.
   !smul:O->O->K->M->M.
   !x:O.
     is_field zeroK oneK addK mulK negK invK /\
     is_algebraically_closed zeroK oneK addK mulK /\
     is_preadditive objects hom identity compose zero add neg /\
     is_linear zeroK oneK addK mulK objects hom compose zero add smul /\
     has_kernels objects hom compose zero /\
     is_simple objects hom identity compose zero x /\
     finite_dimensional objects hom zero add smul x x
     ==> ?basis:num->M.
           has_dimension objects hom zero add smul x x 1 basis`;;
