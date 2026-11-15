;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_392:
;; an even natural number whose three centered, even-spaced integer squares
;; sum to 12296 has the stated natural product quotient. This file contains
;; no proof.

(in-package "ACL2")

(defun mathd-algebra-392-statement (n)
  (implies
   (and (natp n)
        (equal (mod n 2) 0)
        (equal (+ (+ (expt (- n 2) 2)
                     (expt n 2))
                  (expt (+ n 2) 2))
               12296))
   (equal (floor (* (* (nfix (- n 2)) n)
                    (+ n 2))
                 8)
          32736)))

(value-triple :itpeval-statement-checked)
:q
