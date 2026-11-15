;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_640:
;; the sum 91145 + 91146 + 91147 + 91148 has natural-number remainder 2
;; modulo 4. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-640-statement ()
  (equal (mod (+ (+ (+ 91145 91146) 91147) 91148) 4)
         2))

(value-triple :itpeval-statement-checked)
:q
