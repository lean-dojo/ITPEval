;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/powm_Powm_binvert_limbqtvc: the verification condition
;; for Newton-style inversion of an odd unsigned 64-bit limb, from an
;; eight-bit inverse through three precision-doubling steps. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Integers in [0, 2^64) are in bijection with the source unsigned 64-bit
;; limbs. The primary Why3 model uses radix 2^64.

(defconst *pbl-radix* 18446744073709551616)

(defun pbl-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value *pbl-radix*)))

(defun pbl-uint64-in-bounds-p (value)
  (pbl-bv64-p value))

;; Every divisor below is positive under its enclosing assumptions, so ACL2
;; FLOOR and MOD agree with Why3 Euclidean division and modulo.

(defun pbl-double-precision-body-p (n1 inv prec)
  (implies
   (and
    (<= 0 n1)
    (<= 0 inv)
    (equal
     (mod (* inv n1)
          (expt 2 prec))
     1)
    (<= 0 (* 2 prec))
    (<= (* 2 prec) 64))
   (equal
    (mod
     (* (mod
         (- (* 2 inv)
            (* inv (* inv n1)))
         *pbl-radix*)
        n1)
     (expt 2 (* 2 prec)))
    1)))

(defun-sk pbl-double-precision-p ()
  (forall (n1 inv prec)
    (implies
     (and
      (integerp n1)
      (integerp inv)
      (integerp prec))
     (pbl-double-precision-body-p
      n1 inv prec))))

;; The following predicates preserve the source continuation quantifier for
;; each unsigned 64-bit intermediate produced by the three Newton updates.

(defun pbl-o14-body-p (n o13 o12 o14)
  (implies
   (equal
    o14
    (mod (- o13 o12) *pbl-radix*))
   (equal
    (mod (* o14 n) *pbl-radix*)
    1)))

(defun-sk pbl-all-o14-p (n o13 o12)
  (forall (o14)
    (implies
     (pbl-bv64-p o14)
     (pbl-o14-body-p n o13 o12 o14))))

(defun pbl-o13-body-p (n o10 o12 o13)
  (implies
   (equal
    o13
    (mod (* 2 o10) *pbl-radix*))
   (pbl-all-o14-p n o13 o12)))

(defun-sk pbl-all-o13-p (n o10 o12)
  (forall (o13)
    (implies
     (pbl-bv64-p o13)
     (pbl-o13-body-p n o10 o12 o13))))

(defun pbl-o12-body-p (n o10 o11 o12)
  (implies
   (equal
    o12
    (mod (* o10 o11) *pbl-radix*))
   (pbl-all-o13-p n o10 o12)))

(defun-sk pbl-all-o12-p (n o10 o11)
  (forall (o12)
    (implies
     (pbl-bv64-p o12)
     (pbl-o12-body-p n o10 o11 o12))))

(defun pbl-o11-body-p (n o10 o11)
  (implies
   (equal
    o11
    (mod (* o10 n) *pbl-radix*))
   (pbl-all-o12-p n o10 o11)))

(defun-sk pbl-all-o11-p (n o10)
  (forall (o11)
    (implies
     (pbl-bv64-p o11)
     (pbl-o11-body-p n o10 o11))))

(defun pbl-o10-body-p (n o9 o8 o10)
  (implies
   (equal
    o10
    (mod (- o9 o8) *pbl-radix*))
   (pbl-all-o11-p n o10)))

(defun-sk pbl-all-o10-p (n o9 o8)
  (forall (o10)
    (implies
     (pbl-bv64-p o10)
     (pbl-o10-body-p n o9 o8 o10))))

(defun pbl-o9-body-p (n o6 o8 o9)
  (implies
   (equal
    o9
    (mod (* 2 o6) *pbl-radix*))
   (pbl-all-o10-p n o9 o8)))

(defun-sk pbl-all-o9-p (n o6 o8)
  (forall (o9)
    (implies
     (pbl-bv64-p o9)
     (pbl-o9-body-p n o6 o8 o9))))

(defun pbl-o8-body-p (n o6 o7 o8)
  (implies
   (equal
    o8
    (mod (* o6 o7) *pbl-radix*))
   (pbl-all-o9-p n o6 o8)))

(defun-sk pbl-all-o8-p (n o6 o7)
  (forall (o8)
    (implies
     (pbl-bv64-p o8)
     (pbl-o8-body-p n o6 o7 o8))))

(defun pbl-o7-body-p (n o6 o7)
  (implies
   (equal
    o7
    (mod (* o6 n) *pbl-radix*))
   (pbl-all-o8-p n o6 o7)))

(defun-sk pbl-all-o7-p (n o6)
  (forall (o7)
    (implies
     (pbl-bv64-p o7)
     (pbl-o7-body-p n o6 o7))))

(defun pbl-o6-body-p (n o5 o4 o6)
  (implies
   (equal
    o6
    (mod (- o5 o4) *pbl-radix*))
   (pbl-all-o7-p n o6)))

(defun-sk pbl-all-o6-p (n o5 o4)
  (forall (o6)
    (implies
     (pbl-bv64-p o6)
     (pbl-o6-body-p n o5 o4 o6))))

(defun pbl-o5-body-p (n o2 o4 o5)
  (implies
   (equal
    o5
    (mod (* 2 o2) *pbl-radix*))
   (pbl-all-o6-p n o5 o4)))

(defun-sk pbl-all-o5-p (n o2 o4)
  (forall (o5)
    (implies
     (pbl-bv64-p o5)
     (pbl-o5-body-p n o2 o4 o5))))

(defun pbl-o4-body-p (n o2 o3 o4)
  (implies
   (equal
    o4
    (mod (* o2 o3) *pbl-radix*))
   (pbl-all-o5-p n o2 o4)))

(defun-sk pbl-all-o4-p (n o2 o3)
  (forall (o4)
    (implies
     (pbl-bv64-p o4)
     (pbl-o4-body-p n o2 o3 o4))))

(defun pbl-o3-body-p (n o2 o3)
  (implies
   (equal
    o3
    (mod (* o2 n) *pbl-radix*))
   (pbl-all-o4-p n o2 o3)))

(defun-sk pbl-all-o3-p (n o2)
  (forall (o3)
    (implies
     (pbl-bv64-p o3)
     (pbl-o3-body-p n o2 o3))))

;; The table contract supplies an eight-bit inverse of 2*h+1.

(defun pbl-o2-body-p (n h o2)
  (implies
   (and
    (<= 0 o2)
    (< o2 256)
    (equal
     (mod
      (* o2 (+ (* 2 h) 1))
      (expt 2 8))
     1))
   (pbl-all-o3-p n o2)))

(defun-sk pbl-all-o2-p (n h)
  (forall (o2)
    (implies
     (pbl-bv64-p o2)
     (pbl-o2-body-p n h o2))))

;; The primary Why3 program computes h = (n / 2) mod 128.

(defun pbl-h-body-p (n o1 h)
  (implies
   (equal h (mod o1 128))
   (and
    (<= 0 h)
    (< h 128)
    (pbl-all-o2-p n h))))

(defun-sk pbl-all-h-p (n o1)
  (forall (h)
    (implies
     (pbl-bv64-p h)
     (pbl-h-body-p n o1 h))))

(defun pbl-o1-body-p (n o1)
  (implies
   (equal o1 (floor n 2))
   (and
    (not (equal 128 0))
    (pbl-uint64-in-bounds-p
     (mod o1 128))
    (pbl-all-h-p n o1))))

(defun-sk pbl-all-o1-p (n)
  (forall (o1)
    (implies
     (pbl-bv64-p o1)
     (pbl-o1-body-p n o1))))

(defun
    ntp4vc-pearl-multiprecision-powm-powm-binvert-limbqtvc-statement
    (n)
  (implies
   (and
    (pbl-bv64-p n)
    (oddp n))
   (and
    (pbl-double-precision-p)
    (not (equal 2 0))
    (pbl-uint64-in-bounds-p
     (floor n 2))
    (pbl-all-o1-p n))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
