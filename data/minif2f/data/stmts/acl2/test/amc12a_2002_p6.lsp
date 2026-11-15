;; Statement-only formalization of miniF2F corpus artifact amc12a_2002_p6:
;; every positive natural number n has a natural m greater than n and a
;; natural p satisfying m*p <= m+p. The two witnesses remain genuinely
;; existential and are not restricted to preselected finite search ranges.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk amc12a-2002-p6-exists-p (m)
  (exists (p)
    (and (natp p)
         (<= (* m p) (+ m p)))))

(defun-sk amc12a-2002-p6-exists-m (n)
  (exists (m)
    (and (natp m)
         (< n m)
         (amc12a-2002-p6-exists-p m))))

(defun amc12a-2002-p6-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (amc12a-2002-p6-exists-m n)))

(value-triple :itpeval-statement-checked)
:q
