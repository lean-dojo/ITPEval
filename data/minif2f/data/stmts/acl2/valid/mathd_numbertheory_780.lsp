;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_780:
;; a nonnegative integer whose stated congruences hold for a two-digit modulus
;; forces that modulus to equal 43. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-780-statement (m x)
  (implies
   (and (integerp m)
        (integerp x)
        (<= 0 x)
        (<= 10 m)
        (<= m 99)
        (equal (mod (* 6 x) m) 1)
        (equal (mod (- x (expt 6 2)) m) 0))
   (equal m 43)))

(value-triple :itpeval-statement-checked)
:q
