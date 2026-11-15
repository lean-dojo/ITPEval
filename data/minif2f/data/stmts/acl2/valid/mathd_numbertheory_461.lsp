;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_461: for every natural number n equal to the count of
;; integers from 1 through 7 that are coprime to 8, 3^n has remainder 1
;; modulo 8. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-461-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((<= a b)
             (mathd-numbertheory-461-gcd a (- b a)))
            (t
             (mathd-numbertheory-461-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-461-coprime-count-through (limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      0
    (+ (if (equal (mathd-numbertheory-461-gcd limit 8) 1)
           1
         0)
       (mathd-numbertheory-461-coprime-count-through
        (- limit 1)))))

(defun mathd-numbertheory-461-statement (n)
  (implies
   (and (natp n)
        (equal
         n
         (mathd-numbertheory-461-coprime-count-through 7)))
   (equal (mod (expt 3 n) 8)
          1)))

(value-triple :itpeval-statement-checked)
:q
