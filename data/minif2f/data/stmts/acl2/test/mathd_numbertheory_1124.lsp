;; Statement-only formalization of miniF2F artifact mathd_numbertheory_1124:
;; every natural number n at most 9 for which 18 divides 374 * 10 + n is 4.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-1124-statement (n)
  (implies (and (natp n)
                (<= n 9)
                (equal (mod (+ (* 374 10) n) 18) 0))
           (equal n 4)))

(value-triple :itpeval-statement-checked)
:q
