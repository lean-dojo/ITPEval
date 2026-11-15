;; Statement-only formalization of miniF2F corpus artifact amc12b_2020_p21:
;; the set of all positive natural numbers n for which (n + 1000) / 70 equals
;; the floor of the real square root of n has cardinality six. The set is
;; represented extensionally, without imposing a derived numerical cutoff.
;; This file contains no proof.

(in-package "ACL2")

;; For positive natural n, let k = (n + 1000) / 70. The source equation holds
;; exactly when k is a nonnegative integer and k^2 <= n < (k + 1)^2.
(defun amc12b-2020-p21-solution-p (n)
  (and (natp n)
       (< 0 n)
       (let ((k (/ (+ n 1000) 70)))
         (and (integerp k)
              (<= 0 k)
              (<= (* k k) n)
              (< n (* (+ k 1) (+ k 1)))))))

(defun-sk amc12b-2020-p21-complete-solution-set-p (solutions)
  (forall (n)
    (iff (member-equal n solutions)
         (amc12b-2020-p21-solution-p n))))

(defun amc12b-2020-p21-statement (solutions)
  (implies
   (and (true-listp solutions)
        (no-duplicatesp-equal solutions)
        (amc12b-2020-p21-complete-solution-set-p solutions))
   (equal (len solutions) 6)))

(value-triple :itpeval-statement-checked)
:q
