;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_136:
;; a natural number n satisfying 123 * n + 17 = 39500 must equal 321.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-136-statement (n)
  (implies (and (natp n)
                (equal (+ (* 123 n) 17) 39500))
           (equal n 321)))

(value-triple :itpeval-statement-checked)
:q
