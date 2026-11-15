;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_412:
;; for integers x and y congruent to 4 and 7 modulo 19, respectively,
;; (x + 1)^2 * (y + 5)^3 has remainder 13 modulo 19. This file contains no
;; proof.

(in-package "ACL2")

(defun mathd-numbertheory-412-statement (x y)
  (implies
   (and (integerp x)
        (integerp y)
        (equal (mod x 19) 4)
        (equal (mod y 19) 7))
   (equal
    (mod (* (expt (+ x 1) 2)
            (expt (+ y 5) 3))
         19)
    13)))

(value-triple :itpeval-statement-checked)
:q
