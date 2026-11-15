;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_293: a natural number at most 9 for which
;; 20 * 100 + 10 * n + 7 is divisible by 11 must equal 5.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-293-statement (n)
  (implies
   (and (natp n)
        (<= n 9)
        (equal (mod (+ (* 20 100)
                       (* 10 n)
                       7)
                    11)
               0))
   (equal n 5)))

(value-triple :itpeval-statement-checked)
:q
