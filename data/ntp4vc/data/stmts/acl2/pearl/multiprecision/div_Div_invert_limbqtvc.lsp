;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/div_Div_invert_limbqtvc: the verification condition
;; that division of the maximal 64-bit limb and its divisor complement by a
;; normalized divisor produces the prescribed reciprocal limb. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Canonical integers in [0, 2^64) are in bijection with the source unsigned
;; 64-bit words, so unsigned conversion is ordinary integer identity.

(defconst *dili-radix* 18446744073709551616)

(defun dili-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value *dili-radix*)))

(defun dili-uint64-in-bounds-p (value)
  (dili-bv64-p value))

;; The normalized-divisor hypothesis makes every divisor below positive.
;; Hence ACL2 FLOOR agrees with the source Euclidean integer division.

(defun dili-reciprocal-p (v d)
  (equal
   v
   (-
    (floor
     (- (* *dili-radix* *dili-radix*) 1)
     d)
    *dili-radix*)))

;; Preserve the innermost universal quantifier over every possible 64-bit
;; quotient limb.

(defun dili-v-body-p (v d o2)
  (implies
   (equal
    v
    (floor
     (+ (- *dili-radix* 1)
        (* *dili-radix* o2))
     d))
   (dili-reciprocal-p v d)))

(defun-sk dili-all-v-p (d o2)
  (forall (v)
    (implies
     (dili-bv64-p v)
     (dili-v-body-p v d o2))))

;; Preserve the source continuation quantifier for the divisor complement.

(defun dili-o2-body-p (o2 d)
  (implies
   (equal o2 (- (- *dili-radix* 1) d))
   (and
    (< o2 d)
    (dili-all-v-p d o2))))

(defun-sk dili-all-o2-p (d)
  (forall (o2)
    (implies
     (dili-bv64-p o2)
     (dili-o2-body-p o2 d))))

(defun
    ntp4vc-pearl-multiprecision-div-div-invert-limbqtvc-statement
    (d)
  (implies
   (and
    (dili-bv64-p d)
    (<= (floor *dili-radix* 2) d))
   (and
    (dili-uint64-in-bounds-p
     (- (- *dili-radix* 1) d))
    (dili-all-o2-p d))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
