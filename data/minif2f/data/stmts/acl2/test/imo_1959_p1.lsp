;; Statement-only formalization of miniF2F corpus artifact imo_1959_p1:
;; for every natural number n, the greatest common divisor of 21*n + 4 and
;; 14*n + 3 is 1. This file contains no proof.

(in-package "ACL2")

(defun imo-1959-p1-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (imo-1959-p1-gcd a (- b a)))
            (t
             (imo-1959-p1-gcd (- a b) b)))
    0))

(defun imo-1959-p1-statement (n)
  (implies
   (natp n)
   (equal
    (imo-1959-p1-gcd (+ (* 21 n) 4)
                      (+ (* 14 n) 3))
    1)))

(value-triple :itpeval-statement-checked)
:q
