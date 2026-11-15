;; Statement-only formalization of miniF2F corpus artifact amc12a_2009_p15:
;; a positive natural number n whose complex sum from k = 1 through n of
;; k*i^k equals 48 + 49*i must equal 97. This file contains no proof.

(in-package "ACL2")

(defun amc12a-2009-p15-sum-through (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (amc12a-2009-p15-sum-through (- n 1))
       (* n (expt #c(0 1) n)))))

(defun amc12a-2009-p15-statement (n)
  (implies
   (and (natp n)
        (< 0 n)
        (equal (amc12a-2009-p15-sum-through n)
               (+ 48 (* 49 #c(0 1)))))
   (equal n 97)))

(value-triple :itpeval-statement-checked)
:q
