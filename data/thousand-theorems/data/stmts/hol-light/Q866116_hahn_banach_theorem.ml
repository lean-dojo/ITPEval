(*
  Statement-only formalization of Thousand Theorems corpus artifact Q866116,
  "Hahn–Banach theorem": every continuous linear functional on a subspace of
  a seminormed space over an RCLike field extends to the whole space with the
  same operator norm. This file contains no proof.
*)

let Q866116_HAHN_BANACH_THEOREM =
 `let cadd =
    \(z:real#real) (w:real#real).
       (FST z + FST w,SND z + SND w) in
  let cmul =
    \(z:real#real) (w:real#real).
       (FST z * FST w - SND z * SND w,
        FST z * SND w + SND z * FST w) in
  let cneg =
    \(z:real#real). (--(FST z),--(SND z)) in
  let czero = (&0,&0) in
  let cone = (&1,&0) in
  let cmod =
    \(z:real#real). sqrt(FST z pow 2 + SND z pow 2) in
  let real_field_equiv =
    \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
     (negK:K->K) (normK:K->real).
       ?to_real:K->real. ?from_real:real->K.
         (!x:K. from_real (to_real x) = x) /\
         (!r:real. to_real (from_real r) = r) /\
         to_real zeroK = &0 /\
         to_real oneK = &1 /\
         (!x y:K. to_real (addK x y) = to_real x + to_real y) /\
         (!x y:K. to_real (mulK x y) = to_real x * to_real y) /\
         (!x:K. to_real (negK x) = --(to_real x)) /\
         (!x:K. normK x = abs(to_real x)) in
  let complex_field_equiv =
    \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
     (negK:K->K) (normK:K->real).
       ?to_complex:K->real#real. ?from_complex:(real#real)->K.
         (!x:K. from_complex (to_complex x) = x) /\
         (!z:real#real. to_complex (from_complex z) = z) /\
         to_complex zeroK = czero /\
         to_complex oneK = cone /\
         (!x y:K.
            to_complex (addK x y) =
            cadd (to_complex x) (to_complex y)) /\
         (!x y:K.
            to_complex (mulK x y) =
            cmul (to_complex x) (to_complex y)) /\
         (!x:K. to_complex (negK x) = cneg (to_complex x)) /\
         (!x:K. normK x = cmod (to_complex x)) in
  let rclike_normed_field =
    \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
     (negK:K->K) (normK:K->real).
       real_field_equiv zeroK oneK addK mulK negK normK \/
       complex_field_equiv zeroK oneK addK mulK negK normK in
  let seminormed_space =
    \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
     (normK:K->real)
     (zeroE:E) (addE:E->E->E) (negE:E->E)
     (smul:K->E->E) (normE:E->real).
       (!x y z:E. addE x (addE y z) = addE (addE x y) z) /\
       (!x y:E. addE x y = addE y x) /\
       (!x:E. addE zeroE x = x) /\
       (!x:E. addE (negE x) x = zeroE) /\
       normE zeroE = &0 /\
       (!x:E. &0 <= normE x) /\
       (!x:E. normE (negE x) = normE x) /\
       (!x y:E. normE (addE x y) <= normE x + normE y) /\
       (!x:E. smul oneK x = x) /\
       (!a b:K. !x:E. smul (mulK a b) x = smul a (smul b x)) /\
       (!a b:K. !x:E.
          smul (addK a b) x = addE (smul a x) (smul b x)) /\
       (!a:K. !x y:E.
          smul a (addE x y) = addE (smul a x) (smul a y)) /\
       (!a:K. smul a zeroE = zeroE) /\
       (!x:E. smul zeroK x = zeroE) /\
       (!a:K. !x:E. normE (smul a x) = normK a * normE x) in
  let subspace =
    \(zeroE:E) (addE:E->E->E) (smul:K->E->E) (p:E->bool).
       zeroE IN p /\
       (!x y:E. x IN p /\ y IN p ==> addE x y IN p) /\
       (!a:K. !x:E. x IN p ==> smul a x IN p) in
  let continuous_linear_on =
    \(addK:K->K->K) (mulK:K->K->K) (normK:K->real)
     (addE:E->E->E) (smul:K->E->E) (normE:E->real)
     (p:E->bool) (f:E->K).
       (!x y:E.
          x IN p /\ y IN p ==> f (addE x y) = addK (f x) (f y)) /\
       (!a:K. !x:E.
          x IN p ==> f (smul a x) = mulK a (f x)) /\
       (?C:real.
          &0 <= C /\
          !x:E. x IN p ==> normK (f x) <= C * normE x) in
  let operator_norm =
    \(normK:K->real) (normE:E->real)
     (p:E->bool) (f:E->K) (r:real).
       &0 <= r /\
       (!x:E. x IN p ==> normK (f x) <= r * normE x) /\
       (!C:real.
          &0 <= C /\
          (!x:E. x IN p ==> normK (f x) <= C * normE x)
          ==> r <= C) in
  !zeroK oneK:K.
  !addK mulK:K->K->K.
  !negK:K->K.
  !normK:K->real.
  !zeroE:E.
  !addE:E->E->E.
  !negE:E->E.
  !smul:K->E->E.
  !normE:E->real.
  !p:E->bool.
  !f:E->K.
    rclike_normed_field zeroK oneK addK mulK negK normK /\
    seminormed_space
      zeroK oneK addK mulK normK zeroE addE negE smul normE /\
    subspace zeroE addE smul p /\
    continuous_linear_on
      addK mulK normK addE smul normE p f
    ==> ?g:E->K. ?r:real.
          continuous_linear_on
            addK mulK normK addE smul normE (UNIV:E->bool) g /\
          (!x:E. x IN p ==> g x = f x) /\
          operator_norm normK normE p f r /\
          operator_norm normK normE (UNIV:E->bool) g r`;;
