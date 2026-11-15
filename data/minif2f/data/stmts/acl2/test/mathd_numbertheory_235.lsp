;; Statement-only formalization of miniF2F artifact mathd_numbertheory_235:
;; the natural-number remainder of 29 times 79 plus 31 times 81 modulo 10 is 2.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-235-statement ()
  (equal (mod (+ (* 29 79) (* 31 81)) 10) 2))

(value-triple :itpeval-statement-checked)
:q
