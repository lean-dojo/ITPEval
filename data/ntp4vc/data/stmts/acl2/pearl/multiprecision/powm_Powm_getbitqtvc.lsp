;; Statement-only formalization of the NTP4VC corpus artifact
;; pearl/multiprecision/powm_Powm_getbitqtvc: the verification condition for
;; extracting one bit from a multiprecision integer and relating it to the
;; bit-prefix value recurrence. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Canonical integers in [0, 2^w) represent source bitvectors exactly.

(defconst *gbq-radix* 18446744073709551616)

(defun gbq-bv32-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 4294967296)))

(defun gbq-bv64-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x *gbq-radix*)))

(defun gbq-sint32 (x)
  (if (< x 2147483648)
      x
    (- x 4294967296)))

(defun gbq-int32-in-bounds-p (x)
  (and
   (integerp x)
   (<= -2147483648 x)
   (<= x 2147483647)))

(defun gbq-uint64-in-bounds-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (<= x 18446744073709551615)))

;; A source pointer is represented by its observable data and metadata.

(defun gbq-bv64-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and
     (gbq-bv64-p (car xs))
     (gbq-bv64-list-p (cdr xs)))))

(defun gbq-ptr64-p (p)
  (and
   (true-listp p)
   (equal (len p) 7)
   (equal (car p) :gbq-ptr64)
   (gbq-bv64-list-p (cadr p))
   (integerp (caddr p))
   (integerp (cadddr p))
   (integerp (car (cddddr p)))
   (booleanp (cadr (cddddr p)))))

(defun gbq-data (p)
  (cadr p))

(defun gbq-offset (p)
  (caddr p))

(defun gbq-min (p)
  (cadddr p))

(defun gbq-max (p)
  (car (cddddr p)))

(defun gbq-writable (p)
  (cadr (cddddr p)))

(defun gbq-zone (p)
  (caddr (cddddr p)))

(defun gbq-index (i)
  (if (and (integerp i) (< 0 i))
      i
    0))

(defun gbq-pelt64 (p i)
  (let ((n (gbq-index i)))
    (if (< n (len (gbq-data p)))
        (nth n (gbq-data p))
      0)))

(defun gbq-valid-p (p size)
  (and
   (gbq-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (gbq-min p))
   (<= (gbq-min p) (gbq-offset p))
   (<= (+ (gbq-offset p) size) (gbq-max p))
   (<= (gbq-max p) (len (gbq-data p)))))

;; Why3 machine signed division and remainder truncate toward zero.

(defun gbq-tdiv (x y)
  (if (or
       (not (integerp x))
       (not (integerp y))
       (equal y 0))
      0
    (let ((q (floor (abs x) (abs y))))
      (if (< (* x y) 0)
          (- q)
        q))))

(defun gbq-tmod (x y)
  (- x (* y (gbq-tdiv x y))))

(defun gbq-ipow (base exponent)
  (expt base (nfix exponent)))

(defun gbq-value-count (p start count)
  (if (zp count)
      0
    (+
     (gbq-pelt64 p start)
     (*
      *gbq-radix*
      (gbq-value-count p (+ start 1) (- count 1))))))

(defun gbq-value (p size)
  (gbq-value-count p (gbq-offset p) (nfix size)))

(defun gbq-valueb (p nbits)
  (if (< nbits 0)
      0
    (let* ((i (floor nbits 64))
           (r (- nbits (* 64 i))))
      (+
       (gbq-value p i)
       (*
        (gbq-ipow *gbq-radix* i)
        (mod
         (gbq-pelt64 p (+ (gbq-offset p) i))
         (gbq-ipow 2 r)))))))

(defun-sk gbq-same-pelts-p (p q)
  (forall (k)
    (implies
     (integerp k)
     (equal
      (gbq-pelt64 p k)
      (gbq-pelt64 q k)))))

(defun gbq-shifted-pointer-p (p-prime p o4)
  (and
   (equal
    (gbq-offset p-prime)
    (+ (gbq-offset p) (gbq-sint32 o4)))
   (equal
    (len (gbq-data p-prime))
    (len (gbq-data p)))
   (gbq-same-pelts-p p-prime p)
   (equal (gbq-data p-prime) (gbq-data p))
   (equal (gbq-min p-prime) (gbq-min p))
   (equal (gbq-max p-prime) (gbq-max p))
   (equal (gbq-zone p-prime) (gbq-zone p))
   (equal (gbq-writable p-prime) (gbq-writable p))))

(defun gbq-result-body-p (p pn bi lps result)
  (implies
   (equal result (gbq-tmod lps 2))
   (and
    (<= 0 result)
    (<= result 1)
    (equal
     result
     (mod
      (floor
       (gbq-value p (gbq-sint32 pn))
       (gbq-ipow 2 (- (gbq-sint32 bi) 1)))
      2))
    (equal
     (gbq-valueb p (gbq-sint32 bi))
     (+
      (gbq-valueb p (- (gbq-sint32 bi) 1))
      (*
       (gbq-ipow 2 (- (gbq-sint32 bi) 1))
       result))))))

(defun-sk gbq-all-result-p (p pn bi lps)
  (forall (result)
    (implies
     (gbq-bv64-p result)
     (gbq-result-body-p p pn bi lps result))))

(defun gbq-res-body-p (p pn bi lps res)
  (implies
   (equal res (gbq-tmod lps 2))
   (and
    (not (equal 2 0))
    (and
     (not (equal 2 0))
     (gbq-uint64-in-bounds-p (gbq-tmod lps 2)))
    (gbq-all-result-p p pn bi lps))))

(defun-sk gbq-all-res-p (p pn bi lps)
  (forall (res)
    (implies
     (gbq-bv64-p res)
     (gbq-res-body-p p pn bi lps res))))

(defun gbq-lps-body-p (p pn bi i mi lps)
  (implies
   (equal
    lps
    (floor
     (gbq-pelt64 p (+ (gbq-offset p) (gbq-sint32 i)))
     (gbq-ipow 2 mi)))
   (and
    (not (equal (gbq-ipow 2 mi) 0))
    (and
     (not (equal 2 0))
     (gbq-uint64-in-bounds-p (gbq-tmod lps 2)))
    (gbq-all-res-p p pn bi lps))))

(defun-sk gbq-all-lps-p (p pn bi i mi)
  (forall (lps)
    (implies
     (gbq-bv64-p lps)
     (gbq-lps-body-p p pn bi i mi lps))))

(defun gbq-p-prime-body-p (p pn bi i mi o4 p-prime)
  (implies
   (gbq-shifted-pointer-p p-prime p o4)
   (and
    (<= 0 mi)
    (< mi 64)
    (gbq-all-lps-p p pn bi i mi))))

(defun-sk gbq-all-p-prime-p (p pn bi i mi o4)
  (forall (p-prime)
    (implies
     (gbq-ptr64-p p-prime)
     (gbq-p-prime-body-p p pn bi i mi o4 p-prime))))

(defun gbq-o4-body-p (p pn bi i mi o4)
  (implies
   (equal
    (gbq-sint32 o4)
    (+ (gbq-sint32 i) 1))
   (and
    (<=
     (gbq-min p)
     (+ (gbq-offset p) (gbq-sint32 o4)))
    (<=
     (+ (gbq-offset p) (gbq-sint32 o4))
     (gbq-max p))
    (gbq-all-p-prime-p p pn bi i mi o4))))

(defun-sk gbq-all-o4-p (p pn bi i mi)
  (forall (o4)
    (implies
     (gbq-bv32-p o4)
     (gbq-o4-body-p p pn bi i mi o4))))

(defun gbq-mi-body-p (p pn bi i o3 mi)
  (implies
   (equal mi (gbq-tmod o3 64))
   (and
    (<=
     (gbq-min p)
     (+ (gbq-offset p) (gbq-sint32 i)))
    (<
     (+ (gbq-offset p) (gbq-sint32 i))
     (gbq-max p))
    (gbq-int32-in-bounds-p (+ (gbq-sint32 i) 1))
    (gbq-all-o4-p p pn bi i mi))))

(defun-sk gbq-all-mi-p (p pn bi i o3)
  (forall (mi)
    (implies
     (gbq-bv64-p mi)
     (gbq-mi-body-p p pn bi i o3 mi))))

(defun gbq-o3-body-p (p pn bi i o2 o3)
  (implies
   (equal o3 (gbq-sint32 o2))
   (and
    (not (equal 64 0))
    (gbq-uint64-in-bounds-p (gbq-tmod o3 64))
    (gbq-all-mi-p p pn bi i o3))))

(defun-sk gbq-all-o3-p (p pn bi i o2)
  (forall (o3)
    (implies
     (gbq-bv64-p o3)
     (gbq-o3-body-p p pn bi i o2 o3))))

(defun gbq-o2-body-p (p pn bi i o2)
  (implies
   (equal
    (gbq-sint32 o2)
    (- (gbq-sint32 bi) 1))
   (and
    (<= 0 (gbq-sint32 o2))
    (gbq-all-o3-p p pn bi i o2))))

(defun-sk gbq-all-o2-p (p pn bi i)
  (forall (o2)
    (implies
     (gbq-bv32-p o2)
     (gbq-o2-body-p p pn bi i o2))))

(defun gbq-i-body-p (p pn bi o1 i)
  (implies
   (equal
    (gbq-sint32 i)
    (gbq-tdiv (gbq-sint32 o1) 64))
   (and
    (gbq-int32-in-bounds-p (- (gbq-sint32 bi) 1))
    (gbq-all-o2-p p pn bi i))))

(defun-sk gbq-all-i-p (p pn bi o1)
  (forall (i)
    (implies
     (gbq-bv32-p i)
     (gbq-i-body-p p pn bi o1 i))))

(defun gbq-o1-body-p (p pn bi o1)
  (implies
   (equal
    (gbq-sint32 o1)
    (- (gbq-sint32 bi) 1))
   (and
    (not (equal 64 0))
    (gbq-int32-in-bounds-p
     (gbq-tdiv (gbq-sint32 o1) 64))
    (gbq-all-i-p p pn bi o1))))

(defun-sk gbq-all-o1-p (p pn bi)
  (forall (o1)
    (implies
     (gbq-bv32-p o1)
     (gbq-o1-body-p p pn bi o1))))

(defun
    ntp4vc-pearl-multiprecision-powm-powm-getbitqtvc-statement
    (p pn bi)
  (implies
   (and
    (gbq-ptr64-p p)
    (gbq-bv32-p pn)
    (gbq-bv32-p bi)
    (gbq-valid-p p (gbq-sint32 pn))
    (<= 1 (gbq-sint32 bi))
    (<=
     (floor (+ (gbq-sint32 bi) 63) 64)
     (gbq-sint32 pn)))
   (and
    (gbq-int32-in-bounds-p (- (gbq-sint32 bi) 1))
    (gbq-all-o1-p p pn bi))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
