;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_37:
;; the least common multiple of the natural numbers 9999 and 100001 is
;; 90900909. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-37-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-37-gcd a (- b a)))
            (t
             (mathd-numbertheory-37-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-37-lcm (a b)
  (if (and (natp a) (natp b))
      (if (or (equal a 0) (equal b 0))
          0
        (/ (* a b)
           (mathd-numbertheory-37-gcd a b)))
    0))

(defun mathd-numbertheory-37-statement ()
  (equal (mathd-numbertheory-37-lcm 9999 100001)
         90900909))

(value-triple :itpeval-statement-checked)
:q
