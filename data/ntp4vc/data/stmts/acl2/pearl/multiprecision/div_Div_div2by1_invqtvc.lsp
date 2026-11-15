;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/div_Div_div2by1_invqtvc: the verification condition
;; for reciprocal-based division of a two-limb unsigned integer by a
;; normalized 64-bit divisor, including quotient correction and remainder
;; bounds. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Canonical integers in [0, 2^64) are in bijection with the source 64-bit
;; words, so unsigned conversion is ordinary integer identity.

(defconst *d21i-radix* 18446744073709551616)

(defun d21i-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value *d21i-radix*)))

(defun d21i-uint64-in-bounds-p (value)
  (d21i-bv64-p value))

;; The source Euclidean divisions below have positive divisors under their
;; enclosing hypotheses, where ACL2 FLOOR and MOD agree with Why3 div and mod.

(defun d21i-reciprocal-p (v d)
  (equal
   v
   (-
    (floor
     (- (* *d21i-radix* *d21i-radix*) 1)
     d)
    *d21i-radix*)))

(defun d21i-result-p (quotient remainder d uh ul)
  (and
   (equal
    (+ (* quotient d) remainder)
    (+ ul (* *d21i-radix* uh)))
   (<= 0 remainder)
   (< remainder d)))

;; Continuation after the final non-modular remainder subtraction in the
;; first correction branch.

(defun d21i-o6-body-p (d uh ul o5 o4 o6)
  (implies
   (equal o6 (- o4 d))
   (d21i-result-p o5 o6 d uh ul)))

(defun-sk d21i-all-o6-p (d uh ul o5 o4)
  (forall (o6)
    (implies
     (d21i-bv64-p o6)
     (d21i-o6-body-p d uh ul o5 o4 o6))))

(defun d21i-o5-body-p (d uh ul o3 o4 o5)
  (implies
   (equal o5 (+ o3 1))
   (and
    (d21i-uint64-in-bounds-p (- o4 d))
    (d21i-all-o6-p d uh ul o5 o4))))

(defun-sk d21i-all-o5-p (d uh ul o3 o4)
  (forall (o5)
    (implies
     (d21i-bv64-p o5)
     (d21i-o5-body-p d uh ul o3 o4 o5))))

;; Continuations for the branch that first decrements the candidate quotient
;; modulo 2^64 and adds the divisor modulo 2^64.

(defun d21i-first-o4-body-p (d uh ul o3 o2 o4)
  (implies
   (equal
    o4
    (mod (+ o2 d) *d21i-radix*))
   (if (<= d o4)
       (and
        (d21i-uint64-in-bounds-p (+ o3 1))
        (d21i-all-o5-p d uh ul o3 o4))
     (d21i-result-p o3 o4 d uh ul))))

(defun-sk d21i-all-first-o4-p (d uh ul o3 o2)
  (forall (o4)
    (implies
     (d21i-bv64-p o4)
     (d21i-first-o4-body-p d uh ul o3 o2 o4))))

(defun d21i-first-o3-body-p (d uh ul o1 o2 o3)
  (implies
   (equal
    o3
    (mod (- o1 1) *d21i-radix*))
   (d21i-all-first-o4-p d uh ul o3 o2)))

(defun-sk d21i-all-first-o3-p (d uh ul o1 o2)
  (forall (o3)
    (implies
     (d21i-bv64-p o3)
     (d21i-first-o3-body-p d uh ul o1 o2 o3))))

;; Continuations for the branch that skips the modular correction and performs
;; the final ordinary quotient increment and remainder subtraction.

(defun d21i-second-o4-body-p (d uh ul o3 o2 o4)
  (implies
   (equal o4 (- o2 d))
   (d21i-result-p o3 o4 d uh ul)))

(defun-sk d21i-all-second-o4-p (d uh ul o3 o2)
  (forall (o4)
    (implies
     (d21i-bv64-p o4)
     (d21i-second-o4-body-p d uh ul o3 o2 o4))))

(defun d21i-second-o3-body-p (d uh ul o1 o2 o3)
  (implies
   (equal o3 (+ o1 1))
   (and
    (d21i-uint64-in-bounds-p (- o2 d))
    (d21i-all-second-o4-p d uh ul o3 o2))))

(defun-sk d21i-all-second-o3-p (d uh ul o1 o2)
  (forall (o3)
    (implies
     (d21i-bv64-p o3)
     (d21i-second-o3-body-p d uh ul o1 o2 o3))))

(defun d21i-o2-branches-p (d uh ul sl o1 o2)
  (if (< sl o2)
      (d21i-all-first-o3-p d uh ul o1 o2)
    (if (<= d o2)
        (and
         (d21i-uint64-in-bounds-p (+ o1 1))
         (d21i-all-second-o3-p d uh ul o1 o2))
      (d21i-result-p o1 o2 d uh ul))))

;; The candidate remainder is the modular subtraction of the low input limb
;; and the low product.

(defun d21i-o2-body-p (d uh ul sl o1 p o2)
  (implies
   (equal
    o2
    (mod (- ul p) *d21i-radix*))
   (d21i-o2-branches-p d uh ul sl o1 o2)))

(defun-sk d21i-all-o2-p (d uh ul sl o1 p)
  (forall (o2)
    (implies
     (d21i-bv64-p o2)
     (d21i-o2-body-p d uh ul sl o1 p o2))))

(defun d21i-p-body-p (d uh ul sl o1 p)
  (implies
   (equal
    p
    (mod (* o1 d) *d21i-radix*))
   (d21i-all-o2-p d uh ul sl o1 p)))

(defun-sk d21i-all-p-p (d uh ul sl o1)
  (forall (p)
    (implies
     (d21i-bv64-p p)
     (d21i-p-body-p d uh ul sl o1 p))))

(defun d21i-o1-body-p (d uh ul sl sh o1)
  (implies
   (equal
    o1
    (mod (+ sh 1) *d21i-radix*))
   (d21i-all-p-p d uh ul sl o1)))

(defun-sk d21i-all-o1-p (d uh ul sl sh)
  (forall (o1)
    (implies
     (d21i-bv64-p o1)
     (d21i-o1-body-p d uh ul sl sh o1))))

;; The two add-with-carry calls retain their universally quantified outputs,
;; exact radix equations, and carry ranges.

(defun d21i-sh-cprime-body-p
    (d uh h ul sl c sh c-prime)
  (implies
   (and
    (equal
     (+ sh (* *d21i-radix* c-prime))
     (+ uh h c))
    (<= 0 c-prime)
    (<= c-prime 1))
   (d21i-all-o1-p d uh ul sl sh)))

(defun-sk d21i-all-sh-cprime-p
    (d uh h ul sl c)
  (forall (sh c-prime)
    (implies
     (and
      (d21i-bv64-p sh)
      (d21i-bv64-p c-prime))
     (d21i-sh-cprime-body-p
      d uh h ul sl c sh c-prime))))

(defun d21i-sl-c-body-p
    (d uh l h ul sl c)
  (implies
   (and
    (equal
     (+ sl (* *d21i-radix* c))
     (+ l ul 0))
    (<= 0 c)
    (<= c 1))
   (and
    (<= 0 c)
    (<= c 1)
    (d21i-all-sh-cprime-p
     d uh h ul sl c))))

(defun-sk d21i-all-sl-c-p (d uh l h ul)
  (forall (sl c)
    (implies
     (and
      (d21i-bv64-p sl)
      (d21i-bv64-p c))
     (d21i-sl-c-body-p
      d uh l h ul sl c))))

(defun-sk
    ntp4vc-pearl-multiprecision-div-div-div2by1-invqtvc-statement
    ()
  (forall (d uh v l h ul)
    (implies
     (and
      (d21i-bv64-p d)
      (d21i-bv64-p uh)
      (d21i-bv64-p v)
      (d21i-bv64-p l)
      (d21i-bv64-p h)
      (d21i-bv64-p ul)
      (<= (floor *d21i-radix* 2) d)
      (< uh d)
      (d21i-reciprocal-p v d)
      (equal
       (+ l (* *d21i-radix* h))
       (* v uh)))
     (and
      (<= 0 0)
      (<= 0 1)
      (d21i-all-sl-c-p d uh l h ul)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
