;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_530: positive natural numbers whose ratio lies strictly
;; between 5 and 6 have least-common-multiple to greatest-common-divisor
;; quotient at least 22. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-530-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((<= a b)
             (mathd-numbertheory-530-gcd a (- b a)))
            (t
             (mathd-numbertheory-530-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-530-lcm (a b)
  (if (and (posp a) (posp b))
      (/ (* a b)
         (mathd-numbertheory-530-gcd a b))
    0))

(defun mathd-numbertheory-530-statement (n k)
  (implies
   (and (posp n)
        (posp k)
        (< (/ n k) 6)
        (< 5 (/ n k)))
   (<= 22
       (floor (mathd-numbertheory-530-lcm n k)
              (mathd-numbertheory-530-gcd n k)))))

(value-triple :itpeval-statement-checked)
:q
