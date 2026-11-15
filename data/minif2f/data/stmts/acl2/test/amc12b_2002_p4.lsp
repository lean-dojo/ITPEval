;; Statement-only formalization of miniF2F corpus artifact amc12b_2002_p4:
;; a positive natural number n for which 1/2 + 1/3 + 1/7 + 1/n is an
;; integer must equal 42. This file contains no proof.

(in-package "ACL2")

(defun amc12b-2002-p4-statement (n)
  (implies (and (natp n)
                (< 0 n)
                (integerp (+ (/ 1 2)
                             (/ 1 3)
                             (/ 1 7)
                             (/ 1 n))))
           (equal n 42)))

(value-triple :itpeval-statement-checked)
:q
