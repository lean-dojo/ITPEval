;; Statement-only formalization of PutnamBench corpus artifact putnam_1974_b6:
;; among the subsets of the integers 1 through 1000, the numbers having
;; cardinality congruent to 0, 1, and 2 modulo 3 are respectively
;; (2^1000 - 1)/3, (2^1000 - 1)/3, and (2^1000 - 1)/3 + 1.
;; This file contains no proof.

(in-package "ACL2")

;; A subset of {1,...,1000} is represented by its 1000-bit characteristic
;; number. Codes from 0 through 2^1000 - 1 are therefore in bijection with
;; all source subsets, and the bit count is exactly the subset cardinality.
(defun putnam-1974-b6-subset-cardinality
    (subset-code element-count)
  (declare (xargs :measure (nfix element-count)))
  (if (zp element-count)
      0
    (+ (mod subset-code 2)
       (putnam-1974-b6-subset-cardinality
        (floor subset-code 2)
        (- element-count 1)))))

(defun putnam-1974-b6-count-residue
    (candidate-count element-count residue)
  (declare (xargs :measure (nfix candidate-count)))
  (if (zp candidate-count)
      0
    (let ((subset-code (- candidate-count 1)))
      (+ (if (equal
              (mod
               (putnam-1974-b6-subset-cardinality
                subset-code element-count)
               3)
              residue)
             1
           0)
         (putnam-1974-b6-count-residue
          subset-code element-count residue)))))

(defun putnambench-putnam-1974-b6-statement ()
  (let* ((element-count 1000)
         (subset-count (expt 2 element-count))
         (one-third (floor (- subset-count 1) 3)))
    (and
     (equal
      (putnam-1974-b6-count-residue
       subset-count element-count 0)
      one-third)
     (equal
      (putnam-1974-b6-count-residue
       subset-count element-count 1)
      one-third)
     (equal
      (putnam-1974-b6-count-residue
       subset-count element-count 2)
      (+ one-third 1)))))

(value-triple :itpeval-statement-checked)
:q
