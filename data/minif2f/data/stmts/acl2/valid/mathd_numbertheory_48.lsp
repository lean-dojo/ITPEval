;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_48:
;; every positive natural number b satisfying 3*b^2 + 2*b + 1 = 57 is equal
;; to 4. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-48-statement (b)
  (implies
   (and (natp b)
        (< 0 b)
        (equal (+ (* 3 (expt b 2))
                  (* 2 b)
                  1)
               57))
   (equal b 4)))

(value-triple :itpeval-statement-checked)
:q
