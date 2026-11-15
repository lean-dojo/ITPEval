(*
  Statement-only formalization of Thousand Theorems corpus artifact Q213603
  (thousand-theorems__hol-light__Q213603), "Ceva's theorem": for an affinely
  independent triangle over an arbitrary normed field, concurrent lines from
  the vertices through points on the opposite side-lines give a product of
  three nonzero-denominator distance ratios equal to one. This file contains
  no proof.
*)

let Q213603_CEVA_S_THEOREM =
 `let normed_field =
    \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
     (negK:K->K) (invK:K->K) (normK:K->real).
       ~(zeroK = oneK) /\
       (!a b c:K. addK a (addK b c) = addK (addK a b) c) /\
       (!a b:K. addK a b = addK b a) /\
       (!a:K. addK zeroK a = a) /\
       (!a:K. addK (negK a) a = zeroK) /\
       (!a b c:K. mulK a (mulK b c) = mulK (mulK a b) c) /\
       (!a b:K. mulK a b = mulK b a) /\
       (!a:K. mulK oneK a = a) /\
       (!a:K. mulK zeroK a = zeroK) /\
       (!a b c:K.
          mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
       invK zeroK = zeroK /\
       (!a:K. ~(a = zeroK) ==> mulK (invK a) a = oneK) /\
       normK zeroK = &0 /\
       (!a:K. &0 <= normK a) /\
       (!a:K. normK a = &0 <=> a = zeroK) /\
       (!a:K. normK (negK a) = normK a) /\
       (!a b:K. normK (addK a b) <= normK a + normK b) /\
       (!a b:K. normK (mulK a b) = normK a * normK b) in
  let seminormed_add_comm_group =
    \(zeroV:V) (addV:V->V->V) (negV:V->V) (normV:V->real).
       (!x y z:V. addV x (addV y z) = addV (addV x y) z) /\
       (!x y:V. addV x y = addV y x) /\
       (!x:V. addV zeroV x = x) /\
       (!x:V. addV (negV x) x = zeroV) /\
       normV zeroV = &0 /\
       (!x:V. &0 <= normV x) /\
       (!x:V. normV (negV x) = normV x) /\
       (!x y:V. normV (addV x y) <= normV x + normV y) in
  let normed_space =
    \(oneK:K) (addK:K->K->K) (mulK:K->K->K) (normK:K->real)
     (addV:V->V->V) (smul:K->V->V) (normV:V->real).
       (!x:V. smul oneK x = x) /\
       (!a b:K. !x:V. smul (mulK a b) x = smul a (smul b x)) /\
       (!a b:K. !x:V.
          smul (addK a b) x = addV (smul a x) (smul b x)) /\
       (!a:K. !x y:V.
          smul a (addV x y) = addV (smul a x) (smul a y)) /\
       (!a:K. !x:V. normV (smul a x) <= normK a * normV x) in
  let metric_affine_torsor =
    \(zeroV:V) (addV:V->V->V) (normV:V->real)
     (vadd:V->P->P) (vsub:P->P->V).
       (!q:P. vadd zeroV q = q) /\
       (!v w:V. !q:P.
          vadd (addV v w) q = vadd v (vadd w q)) /\
       (!v:V. !q:P. vsub (vadd v q) q = v) /\
       (!q r:P. vadd (vsub q r) r = q) /\
       (!q r:P. normV (vsub q r) = &0 <=> q = r) in
  let affine_independent_triangle =
    \(zeroK:K) (zeroV:V) (addV:V->V->V) (smul:K->V->V)
     (vsub:P->P->V) (t0:P) (t1:P) (t2:P).
       !a b:K.
         addV (smul a (vsub t1 t0)) (smul b (vsub t2 t0)) = zeroV
         ==> a = zeroK /\ b = zeroK in
  let on_line =
    \(smul:K->V->V) (vadd:V->P->P) (vsub:P->P->V)
     (a:P) (b:P) (x:P).
       ?r:K. vadd (smul r (vsub b a)) a = x in
  let distance =
    \(normV:V->real) (vsub:P->P->V) (q:P) (r:P).
       normV (vsub q r) in
  !zeroK oneK:K.
  !addK mulK:K->K->K.
  !negK invK:K->K.
  !normK:K->real.
  !zeroV:V.
  !addV:V->V->V.
  !negV:V->V.
  !normV:V->real.
  !smul:K->V->V.
  !vadd:V->P->P.
  !vsub:P->P->V.
  !t0 t1 t2 p0 p1 p2 p':P.
    normed_field zeroK oneK addK mulK negK invK normK /\
    seminormed_add_comm_group zeroV addV negV normV /\
    normed_space oneK addK mulK normK addV smul normV /\
    metric_affine_torsor zeroV addV normV vadd vsub /\
    affine_independent_triangle zeroK zeroV addV smul vsub t0 t1 t2 /\
    ~(p0 = t2) /\ ~(p1 = t0) /\ ~(p2 = t1) /\
    on_line smul vadd vsub t1 t2 p0 /\
    on_line smul vadd vsub t2 t0 p1 /\
    on_line smul vadd vsub t0 t1 p2 /\
    on_line smul vadd vsub t0 p0 p' /\
    on_line smul vadd vsub t1 p1 p' /\
    on_line smul vadd vsub t2 p2 p'
    ==>
    (distance normV vsub t1 p0 / distance normV vsub p0 t2) *
    (distance normV vsub t2 p1 / distance normV vsub p1 t0) *
    (distance normV vsub t0 p2 / distance normV vsub p2 t1) = &1`;;
