;; Statement-only formalization of PutnamBench corpus artifact putnam_1993_b1:
;; 3987 is the least positive integer n such that every integer m with
;; 0 < m < 1993 admits an integer k strictly between the specified rational
;; bounds m/1993 and (m+1)/1994 after division by n. This file contains no proof.

(in-package "ACL2")

;; For positive n and 0 < m < 1993, any integer k satisfying the source
;; inequalities must have 0 < k < n: the lower bound is positive and the upper
;; bound is less than one. Conversely every possible source witness is
;; therefore included in this finite search. ACL2's rational comparisons agree
;; with the same inequalities after embedding these rational values in R.
(defun putnam-1993-b1-witness-through-p (n m candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (and (posp n)
           (natp m)
           (natp candidate))
      (or (and (< (/ m 1993)
                  (/ candidate n))
               (< (/ candidate n)
                  (/ (+ m 1) 1994)))
          (and (not (zp candidate))
               (putnam-1993-b1-witness-through-p
                n m (- candidate 1))))
    nil))

;; Called with m=1992, this is the universal quantifier over exactly the
;; integers 0 < m < 1993, with each existential k kept internal.
(defun putnam-1993-b1-all-m-through-p (n m)
  (declare (xargs :measure (nfix m)))
  (if (and (posp n)
           (natp m))
      (if (zp m)
          t
        (and (putnam-1993-b1-witness-through-p
              n m (- n 1))
             (putnam-1993-b1-all-m-through-p
              n (- m 1))))
    nil))

(defun putnam-1993-b1-condition-p (n)
  (and (posp n)
       (putnam-1993-b1-all-m-through-p n 1992)))

;; Since the condition itself requires positivity, the assertion that every
;; solution is at least 3987 is equivalent to checking that none of the
;; positive integers through 3986 satisfies it.
(defun putnam-1993-b1-no-solution-through-p (candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (natp candidate)
      (if (zp candidate)
          t
        (and (not (putnam-1993-b1-condition-p candidate))
             (putnam-1993-b1-no-solution-through-p
              (- candidate 1))))
    nil))

(defun putnambench-putnam-1993-b1-statement ()
  (and (putnam-1993-b1-condition-p 3987)
       (putnam-1993-b1-no-solution-through-p 3986)))

(value-triple :itpeval-statement-checked)
:q
