;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bitcount_Hamming_hammingDqtvc: the 32-bit Hamming-distance
;; verification condition relating the population count of XOR to the number
;; of differing bit positions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^32 are in bijection with the source's 32-bit words.

(defun hammingqtvc-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value (expt 2 32))))

;; The source nth_closure reads a bit after converting its integer index to a
;; natural number.

(defun hammingqtvc-nth-closure (value bit)
  (logbitp (nfix bit) value))

;; This is NumOf.numof specialized to nth_closure: it counts true values on
;; the half-open integer interval [lower, upper).

(defun hammingqtvc-numof-bits (value lower upper)
  (declare
   (xargs
    :measure (nfix (- (ifix upper) (ifix lower)))))
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (+ (if (hammingqtvc-nth-closure value (- upper 1))
             1
           0)
         (hammingqtvc-numof-bits value lower (- upper 1)))
    0))

(defun hammingqtvc-count-logic (value)
  (hammingqtvc-numof-bits value 0 32))

;; Unsigned integer XOR is the source word XOR on 32-bit inputs.

(defun hammingqtvc-xor32 (left right)
  (mod (logxor left right) (expt 2 32)))

;; This directly represents nth_diff: the selected bits of the two words are
;; unequal.

(defun hammingqtvc-nth-diff-p (left right bit)
  (not
   (equal
    (logbitp (nfix bit) left)
    (logbitp (nfix bit) right))))

;; This is NumOf.numof specialized to nth_diff on a half-open interval.

(defun hammingqtvc-numof-differences
    (left right lower upper)
  (declare
   (xargs
    :measure (nfix (- (ifix upper) (ifix lower)))))
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (+ (if
             (hammingqtvc-nth-diff-p
              left right (- upper 1))
             1
           0)
         (hammingqtvc-numof-differences
          left right lower (- upper 1)))
    0))

(defun hammingqtvc-hammingd-logic (left right)
  (hammingqtvc-numof-differences left right 0 32))

(defun
    ntp4vc-pearl-bitcount-hamming-hammingdqtvc-statement
    (result a b)
  (implies
   (and
    (hammingqtvc-bv32-p result)
    (hammingqtvc-bv32-p a)
    (hammingqtvc-bv32-p b))
   (implies
    (equal
     result
     (hammingqtvc-count-logic
      (hammingqtvc-xor32 a b)))
    (equal
     result
     (hammingqtvc-hammingd-logic a b)))))

(value-triple :itpeval-statement-checked)
:q
