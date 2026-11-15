;; Statement-only formalization of miniF2F artifact mathd_numbertheory_188:
;; the natural-number greatest common divisor of 180 and 168 equals 12.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-188-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-188-gcd a (- b a)))
            (t
             (mathd-numbertheory-188-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-188-statement ()
  (equal (mathd-numbertheory-188-gcd 180 168) 12))

(value-triple :itpeval-statement-checked)
:q
