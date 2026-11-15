;; Statement-only formalization of PutnamBench corpus artifact putnam_1990_a6:
;; exactly 17,711 ordered pairs of subsets of {1,...,10} are admissible when
;; every element of either subset exceeds the cardinality of the other.
;; This file contains no proof.

(in-package "ACL2")

;; A subset of {1,...,10} is represented by its 10-bit characteristic
;; number. Codes from 0 through 2^10 - 1 are therefore in bijection with all
;; source subsets, and the recursion through the ten bits gives the exact
;; subset cardinality.
(defun putnam-1990-a6-mask-member-p (element mask)
  (and
   (posp element)
   (<= element 10)
   (natp mask)
   (< mask (expt 2 10))
   (equal
    (mod (floor mask (expt 2 (- element 1))) 2)
    1)))

(defun putnam-1990-a6-cardinality-through
    (mask remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if (putnam-1990-a6-mask-member-p remaining mask)
         1
       0)
     (putnam-1990-a6-cardinality-through
      mask (- remaining 1)))))

(defun putnam-1990-a6-members-exceed-p
    (mask other-cardinality remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (or
      (not (putnam-1990-a6-mask-member-p remaining mask))
      (< other-cardinality remaining))
     (putnam-1990-a6-members-exceed-p
      mask other-cardinality (- remaining 1)))))

(defun putnam-1990-a6-admissible-p (s-code t-code)
  (and
   (natp s-code)
   (< s-code (expt 2 10))
   (natp t-code)
   (< t-code (expt 2 10))
   (let ((s-cardinality
          (putnam-1990-a6-cardinality-through s-code 10))
         (t-cardinality
          (putnam-1990-a6-cardinality-through t-code 10)))
     (and
      (putnam-1990-a6-members-exceed-p
       s-code t-cardinality 10)
      (putnam-1990-a6-members-exceed-p
       t-code s-cardinality 10)))))

(defun putnam-1990-a6-count-t-codes
    (s-code remaining-t-codes)
  (declare (xargs :measure (nfix remaining-t-codes)))
  (if (zp remaining-t-codes)
      0
    (let ((t-code (- remaining-t-codes 1)))
      (+
       (if (putnam-1990-a6-admissible-p s-code t-code)
           1
         0)
       (putnam-1990-a6-count-t-codes s-code t-code)))))

(defun putnam-1990-a6-count-s-codes
    (remaining-s-codes)
  (declare (xargs :measure (nfix remaining-s-codes)))
  (if (zp remaining-s-codes)
      0
    (let ((s-code (- remaining-s-codes 1)))
      (+
       (putnam-1990-a6-count-t-codes
        s-code (expt 2 10))
       (putnam-1990-a6-count-s-codes s-code)))))

(defun putnambench-putnam-1990-a6-statement ()
  (equal
   (putnam-1990-a6-count-s-codes (expt 2 10))
   17711))

(value-triple :itpeval-statement-checked)
:q
