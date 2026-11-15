;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_582:
;; for every positive natural number n divisible by 3, the sum
;; (n + 4) + (n + 6) + (n + 8) is divisible by 9. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-582-statement (n)
  (implies
   (and (natp n)
        (< 0 n)
        (equal (mod n 3) 0))
   (equal
    (mod (+ (+ (+ n 4) (+ n 6))
            (+ n 8))
         9)
    0)))

(value-triple :itpeval-statement-checked)
:q
