;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_227: positive natural numbers x, y, and n satisfying
;; x/4 + y/6 = (x + y)/n must have n = 5. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-227-statement (x y n)
  (implies
   (and (posp x)
        (posp y)
        (posp n)
        (equal (+ (/ x 4)
                  (/ y 6))
               (/ (+ x y) n)))
   (equal n 5)))

(value-triple :itpeval-statement-checked)
:q
