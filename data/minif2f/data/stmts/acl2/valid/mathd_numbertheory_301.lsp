;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_301:
;; for every positive natural number j, 3 * (7*j + 3) has remainder 2 modulo
;; 7. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-301-statement (j)
  (implies (and (natp j)
                (< 0 j))
           (equal (mod (* 3 (+ (* 7 j) 3)) 7)
                  2)))

(value-triple :itpeval-statement-checked)
:q
