;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/div_Div_div3by2_invqtvc: the verification condition
;; for reciprocal-based division of a three-limb unsigned integer by a
;; normalized two-limb 64-bit divisor, including quotient corrections and
;; the final two-limb remainder bound. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Canonical integers in [0, 2^64) are in bijection with the source 64-bit
;; words, so unsigned conversion is ordinary integer identity.

(defconst *d32i-radix* 18446744073709551616)

(defun d32i-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value *d32i-radix*)))

;; Under the statement hypotheses the divisor of FLOOR is positive.  ACL2
;; FLOOR and MOD therefore agree with the source Euclidean div and mod.

(defun d32i-reciprocal-3by2-p (v dh dl)
  (equal
   v
   (-
    (floor
     (- (* *d32i-radix* *d32i-radix* *d32i-radix*) 1)
     (+ dl (* *d32i-radix* dh)))
    *d32i-radix*)))

(defun d32i-result-p (q rl rh dl dh ul um uh)
  (and
   (equal
    (+ (* q dl)
       (* *d32i-radix* q dh)
       rl
       (* *d32i-radix* rh))
    (+ ul
       (* *d32i-radix* um)
       (* *d32i-radix* *d32i-radix* uh)))
   (<= 0 (+ rl (* *d32i-radix* rh)))
   (< (+ rl (* *d32i-radix* rh))
      (+ dl (* *d32i-radix* dh)))))

;; First final-correction branch: after adding the divisor, test whether one
;; more subtraction and quotient increment are required.

(defun d32i-a-final-o5-body-p
    (dl dh ul um uh bl1 bh1 o3 o5)
  (implies
   (equal
    o5
    (mod (+ o3 1) *d32i-radix*))
   (d32i-result-p o5 bl1 bh1 dl dh ul um uh)))

(defun-sk d32i-a-all-final-o5-p
    (dl dh ul um uh bl1 bh1 o3)
  (forall (o5)
    (implies
     (d32i-bv64-p o5)
     (d32i-a-final-o5-body-p
      dl dh ul um uh bl1 bh1 o3 o5))))

(defun d32i-a-bh1-bprime-body-p
    (dl dh ul um uh rh bl1 b1 o3 bh1 b-prime)
  (implies
   (and
    (equal
     (- bh1 (* *d32i-radix* b-prime))
     (- (- rh dh) b1))
    (<= 0 b-prime)
    (<= b-prime 1))
   (d32i-a-all-final-o5-p
    dl dh ul um uh bl1 bh1 o3)))

(defun-sk d32i-a-all-bh1-bprime-p
    (dl dh ul um uh rh bl1 b1 o3)
  (forall (bh1 b-prime)
    (implies
     (and
      (d32i-bv64-p bh1)
      (d32i-bv64-p b-prime))
     (d32i-a-bh1-bprime-body-p
      dl dh ul um uh rh bl1 b1 o3 bh1 b-prime))))

(defun d32i-a-bl1-b1-body-p
    (dl dh ul um uh rl rh o3 bl1 b1)
  (implies
   (and
    (equal
     (- bl1 (* *d32i-radix* b1))
     (- (- rl dl) 0))
    (<= 0 b1)
    (<= b1 1))
   (and
    (<= 0 b1)
    (<= b1 1)
    (d32i-a-all-bh1-bprime-p
     dl dh ul um uh rh bl1 b1 o3))))

(defun-sk d32i-a-all-bl1-b1-p
    (dl dh ul um uh rl rh o3)
  (forall (bl1 b1)
    (implies
     (and
      (d32i-bv64-p bl1)
      (d32i-bv64-p b1))
     (d32i-a-bl1-b1-body-p
      dl dh ul um uh rl rh o3 bl1 b1))))

(defun d32i-a-o4-conclusion-p
    (dl dh ul um uh rl rh o3 o4)
  (if (equal o4 t)
      (and
       (<= 0 0)
       (<= 0 1)
       (d32i-a-all-bl1-b1-p
        dl dh ul um uh rl rh o3))
    (d32i-result-p o3 rl rh dl dh ul um uh)))

(defun-sk d32i-a-o5-condition-exists-p
    (dh rh dl rl o4)
  (exists (o5)
    (and
     (booleanp o5)
     (implies (equal rh dh) (equal o5 t))
     (implies (equal o5 t) (equal rh dh))
     (equal
      o4
      (if (equal o5 t)
          (if (<= dl rl) t nil)
        nil)))))

(defun d32i-a-o4-antecedent-p
    (dh rh dl rl o4)
  (if (< dh rh)
      (equal o4 t)
    (d32i-a-o5-condition-exists-p
     dh rh dl rl o4)))

(defun d32i-a-o4-body-p
    (dl dh ul um uh rl rh o3 o4)
  (implies
   (d32i-a-o4-antecedent-p dh rh dl rl o4)
   (d32i-a-o4-conclusion-p
    dl dh ul um uh rl rh o3 o4)))

(defun-sk d32i-a-all-o4-p
    (dl dh ul um uh rl rh o3)
  (forall (o4)
    (implies
     (booleanp o4)
     (d32i-a-o4-body-p
      dl dh ul um uh rl rh o3 o4))))

(defun d32i-a-rh-cprime-body-p
    (dl dh ul um uh bh rl c1 o3 rh c-prime)
  (implies
   (and
    (equal
     (+ rh (* *d32i-radix* c-prime))
     (+ bh dh c1))
    (<= 0 c-prime)
    (<= c-prime 1))
   (d32i-a-all-o4-p
    dl dh ul um uh rl rh o3)))

(defun-sk d32i-a-all-rh-cprime-p
    (dl dh ul um uh bh rl c1 o3)
  (forall (rh c-prime)
    (implies
     (and
      (d32i-bv64-p rh)
      (d32i-bv64-p c-prime))
     (d32i-a-rh-cprime-body-p
      dl dh ul um uh bh rl c1 o3 rh c-prime))))

(defun d32i-a-rl-c1-body-p
    (dl dh ul um uh bl bh o3 rl c1)
  (implies
   (and
    (equal
     (+ rl (* *d32i-radix* c1))
     (+ bl dl 0))
    (<= 0 c1)
    (<= c1 1))
   (and
    (<= 0 c1)
    (<= c1 1)
    (d32i-a-all-rh-cprime-p
     dl dh ul um uh bh rl c1 o3))))

(defun-sk d32i-a-all-rl-c1-p
    (dl dh ul um uh bl bh o3)
  (forall (rl c1)
    (implies
     (and
      (d32i-bv64-p rl)
      (d32i-bv64-p c1))
     (d32i-a-rl-c1-body-p
      dl dh ul um uh bl bh o3 rl c1))))

(defun d32i-a-o3-body-p
    (dl dh ul um uh bl bh o1 o3)
  (implies
   (equal
    o3
    (mod (- o1 1) *d32i-radix*))
   (and
    (<= 0 0)
    (<= 0 1)
    (d32i-a-all-rl-c1-p
     dl dh ul um uh bl bh o3))))

(defun-sk d32i-a-all-o3-p
    (dl dh ul um uh bl bh o1)
  (forall (o3)
    (implies
     (d32i-bv64-p o3)
     (d32i-a-o3-body-p
      dl dh ul um uh bl bh o1 o3))))

;; Second final-correction branch: test the unrepaired remainder directly.

(defun d32i-b-final-o4-body-p
    (dl dh ul um uh bl1 bh1 o1 o4)
  (implies
   (equal
    o4
    (mod (+ o1 1) *d32i-radix*))
   (d32i-result-p o4 bl1 bh1 dl dh ul um uh)))

(defun-sk d32i-b-all-final-o4-p
    (dl dh ul um uh bl1 bh1 o1)
  (forall (o4)
    (implies
     (d32i-bv64-p o4)
     (d32i-b-final-o4-body-p
      dl dh ul um uh bl1 bh1 o1 o4))))

(defun d32i-b-bh1-bprime-body-p
    (dl dh ul um uh bh bl1 b3 o1 bh1 b-prime)
  (implies
   (and
    (equal
     (- bh1 (* *d32i-radix* b-prime))
     (- (- bh dh) b3))
    (<= 0 b-prime)
    (<= b-prime 1))
   (d32i-b-all-final-o4-p
    dl dh ul um uh bl1 bh1 o1)))

(defun-sk d32i-b-all-bh1-bprime-p
    (dl dh ul um uh bh bl1 b3 o1)
  (forall (bh1 b-prime)
    (implies
     (and
      (d32i-bv64-p bh1)
      (d32i-bv64-p b-prime))
     (d32i-b-bh1-bprime-body-p
      dl dh ul um uh bh bl1 b3 o1 bh1 b-prime))))

(defun d32i-b-bl1-b3-body-p
    (dl dh ul um uh bl bh o1 bl1 b3)
  (implies
   (and
    (equal
     (- bl1 (* *d32i-radix* b3))
     (- (- bl dl) 0))
    (<= 0 b3)
    (<= b3 1))
   (and
    (<= 0 b3)
    (<= b3 1)
    (d32i-b-all-bh1-bprime-p
     dl dh ul um uh bh bl1 b3 o1))))

(defun-sk d32i-b-all-bl1-b3-p
    (dl dh ul um uh bl bh o1)
  (forall (bl1 b3)
    (implies
     (and
      (d32i-bv64-p bl1)
      (d32i-bv64-p b3))
     (d32i-b-bl1-b3-body-p
      dl dh ul um uh bl bh o1 bl1 b3))))

(defun d32i-b-o3-conclusion-p
    (dl dh ul um uh bl bh o1 o3)
  (if (equal o3 t)
      (and
       (<= 0 0)
       (<= 0 1)
       (d32i-b-all-bl1-b3-p
        dl dh ul um uh bl bh o1))
    (d32i-result-p o1 bl bh dl dh ul um uh)))

(defun-sk d32i-b-o4-condition-exists-p
    (dh bh dl bl o3)
  (exists (o4)
    (and
     (booleanp o4)
     (implies (equal bh dh) (equal o4 t))
     (implies (equal o4 t) (equal bh dh))
     (equal
      o3
      (if (equal o4 t)
          (if (<= dl bl) t nil)
        nil)))))

(defun d32i-b-o3-antecedent-p
    (dh bh dl bl o3)
  (if (< dh bh)
      (equal o3 t)
    (d32i-b-o4-condition-exists-p
     dh bh dl bl o3)))

(defun d32i-b-o3-body-p
    (dl dh ul um uh bl bh o1 o3)
  (implies
   (d32i-b-o3-antecedent-p dh bh dl bl o3)
   (d32i-b-o3-conclusion-p
    dl dh ul um uh bl bh o1 o3)))

(defun-sk d32i-b-all-o3-p
    (dl dh ul um uh bl bh o1)
  (forall (o3)
    (implies
     (booleanp o3)
     (d32i-b-o3-body-p
      dl dh ul um uh bl bh o1 o3))))

;; Common multiplication and subtraction continuation preceding the two
;; final-correction branches.

(defun d32i-bh-b2prime-body-p
    (dl dh ul um uh sl o1 ih bl b2 bh b2-prime)
  (implies
   (and
    (equal
     (- bh (* *d32i-radix* b2-prime))
     (- (- ih dh) b2))
    (<= 0 b2-prime)
    (<= b2-prime 1))
   (if (<= sl bh)
       (d32i-a-all-o3-p
        dl dh ul um uh bl bh o1)
     (d32i-b-all-o3-p
      dl dh ul um uh bl bh o1))))

(defun-sk d32i-all-bh-b2prime-p
    (dl dh ul um uh sl o1 ih bl b2)
  (forall (bh b2-prime)
    (implies
     (and
      (d32i-bv64-p bh)
      (d32i-bv64-p b2-prime))
     (d32i-bh-b2prime-body-p
      dl dh ul um uh sl o1 ih bl b2 bh b2-prime))))

(defun d32i-bl-b2-body-p
    (dl dh ul um uh sl o1 il ih bl b2)
  (implies
   (and
    (equal
     (- bl (* *d32i-radix* b2))
     (- (- il dl) 0))
    (<= 0 b2)
    (<= b2 1))
   (and
    (<= 0 b2)
    (<= b2 1)
    (d32i-all-bh-b2prime-p
     dl dh ul um uh sl o1 ih bl b2))))

(defun-sk d32i-all-bl-b2-p
    (dl dh ul um uh sl o1 il ih)
  (forall (bl b2)
    (implies
     (and
      (d32i-bv64-p bl)
      (d32i-bv64-p b2))
     (d32i-bl-b2-body-p
      dl dh ul um uh sl o1 il ih bl b2))))

(defun d32i-ih-bprime-body-p
    (dl dh ul um uh sl o1 o2 th il b ih b-prime)
  (implies
   (and
    (equal
     (- ih (* *d32i-radix* b-prime))
     (- (- o2 th) b))
    (<= 0 b-prime)
    (<= b-prime 1))
   (and
    (<= 0 0)
    (<= 0 1)
    (d32i-all-bl-b2-p
     dl dh ul um uh sl o1 il ih))))

(defun-sk d32i-all-ih-bprime-p
    (dl dh ul um uh sl o1 o2 th il b)
  (forall (ih b-prime)
    (implies
     (and
      (d32i-bv64-p ih)
      (d32i-bv64-p b-prime))
     (d32i-ih-bprime-body-p
      dl dh ul um uh sl o1 o2 th il b ih b-prime))))

(defun d32i-il-b-body-p
    (dl dh ul um uh sl o1 o2 tl th il b)
  (implies
   (and
    (equal
     (- il (* *d32i-radix* b))
     (- (- ul tl) 0))
    (<= 0 b)
    (<= b 1))
   (and
    (<= 0 b)
    (<= b 1)
    (d32i-all-ih-bprime-p
     dl dh ul um uh sl o1 o2 th il b))))

(defun-sk d32i-all-il-b-p
    (dl dh ul um uh sl o1 o2 tl th)
  (forall (il b)
    (implies
     (and
      (d32i-bv64-p il)
      (d32i-bv64-p b))
     (d32i-il-b-body-p
      dl dh ul um uh sl o1 o2 tl th il b))))

(defun d32i-tl-th-body-p
    (dl dh ul um uh sl sh o1 o2 tl th)
  (implies
   (equal
    (+ tl (* *d32i-radix* th))
    (* sh dl))
   (and
    (<= 0 0)
    (<= 0 1)
    (d32i-all-il-b-p
     dl dh ul um uh sl o1 o2 tl th))))

(defun-sk d32i-all-tl-th-p
    (dl dh ul um uh sl sh o1 o2)
  (forall (tl th)
    (implies
     (and
      (d32i-bv64-p tl)
      (d32i-bv64-p th))
     (d32i-tl-th-body-p
      dl dh ul um uh sl sh o1 o2 tl th))))

(defun d32i-o2-body-p
    (dl dh ul um uh sl sh o1 p o2)
  (implies
   (equal
    o2
    (mod (- um p) *d32i-radix*))
   (and
    (not (equal *d32i-radix* 0))
    (d32i-all-tl-th-p
     dl dh ul um uh sl sh o1 o2))))

(defun-sk d32i-all-o2-p
    (dl dh ul um uh sl sh o1 p)
  (forall (o2)
    (implies
     (d32i-bv64-p o2)
     (d32i-o2-body-p
      dl dh ul um uh sl sh o1 p o2))))

(defun d32i-p-body-p
    (dl dh ul um uh sl sh o1 p)
  (implies
   (equal
    p
    (mod (* dh sh) *d32i-radix*))
   (d32i-all-o2-p
    dl dh ul um uh sl sh o1 p)))

(defun-sk d32i-all-p-p
    (dl dh ul um uh sl sh o1)
  (forall (p)
    (implies
     (d32i-bv64-p p)
     (d32i-p-body-p
      dl dh ul um uh sl sh o1 p))))

(defun d32i-o1-body-p
    (dl dh ul um uh sl sh o1)
  (implies
   (equal
    o1
    (mod (+ sh 1) *d32i-radix*))
   (d32i-all-p-p
    dl dh ul um uh sl sh o1)))

(defun-sk d32i-all-o1-p
    (dl dh ul um uh sl sh)
  (forall (o1)
    (implies
     (d32i-bv64-p o1)
     (d32i-o1-body-p
      dl dh ul um uh sl sh o1))))

;; The initial two add-with-carry calls retain their exact radix equations,
;; carry ranges, and universally quantified outputs.

(defun d32i-sh-cprime-body-p
    (dl dh ul um uh h sl c sh c-prime)
  (implies
   (and
    (equal
     (+ sh (* *d32i-radix* c-prime))
     (+ uh h c))
    (<= 0 c-prime)
    (<= c-prime 1))
   (d32i-all-o1-p
    dl dh ul um uh sl sh)))

(defun-sk d32i-all-sh-cprime-p
    (dl dh ul um uh h sl c)
  (forall (sh c-prime)
    (implies
     (and
      (d32i-bv64-p sh)
      (d32i-bv64-p c-prime))
     (d32i-sh-cprime-body-p
      dl dh ul um uh h sl c sh c-prime))))

(defun d32i-sl-c-body-p
    (dl dh ul um uh l h sl c)
  (implies
   (and
    (equal
     (+ sl (* *d32i-radix* c))
     (+ um l 0))
    (<= 0 c)
    (<= c 1))
   (and
    (<= 0 c)
    (<= c 1)
    (d32i-all-sh-cprime-p
     dl dh ul um uh h sl c))))

(defun-sk d32i-all-sl-c-p
    (dl dh ul um uh l h)
  (forall (sl c)
    (implies
     (and
      (d32i-bv64-p sl)
      (d32i-bv64-p c))
     (d32i-sl-c-body-p
      dl dh ul um uh l h sl c))))

(defun-sk
    ntp4vc-pearl-multiprecision-div-div-div3by2-invqtvc-statement
    ()
  (forall (dh v dl um uh l h ul)
    (implies
     (and
      (d32i-bv64-p dh)
      (d32i-bv64-p v)
      (d32i-bv64-p dl)
      (d32i-bv64-p um)
      (d32i-bv64-p uh)
      (d32i-bv64-p l)
      (d32i-bv64-p h)
      (d32i-bv64-p ul)
      (<= (floor *d32i-radix* 2) dh)
      (d32i-reciprocal-3by2-p v dh dl)
      (< (+ um (* *d32i-radix* uh))
         (+ dl (* *d32i-radix* dh)))
      (equal
       (+ l (* *d32i-radix* h))
       (* v uh)))
     (and
      (<= 0 0)
      (<= 0 1)
      (d32i-all-sl-c-p
       dl dh ul um uh l h)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
