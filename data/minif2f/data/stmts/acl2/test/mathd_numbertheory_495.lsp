;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_495: positive natural numbers ending in 2 and 4 whose
;; greatest common divisor is 6 have least common multiple at least 108.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-495-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-495-gcd a (- b a)))
            (t
             (mathd-numbertheory-495-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-495-lcm (a b)
  (if (and (posp a) (posp b))
      (/ (* a b)
         (mathd-numbertheory-495-gcd a b))
    0))

(defun mathd-numbertheory-495-statement (a b)
  (implies
   (and (posp a)
        (posp b)
        (equal (mod a 10) 2)
        (equal (mod b 10) 4)
        (equal (mathd-numbertheory-495-gcd a b) 6))
   (<= 108 (mathd-numbertheory-495-lcm a b))))

(value-triple :itpeval-statement-checked)
:q
