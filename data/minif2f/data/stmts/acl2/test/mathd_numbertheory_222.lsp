;; Statement-only formalization of miniF2F artifact mathd_numbertheory_222:
;; for every natural number b, lcm(120, b) = 3720 and gcd(120, b) = 8 imply
;; b = 248. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-222-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-222-gcd a (- b a)))
            (t
             (mathd-numbertheory-222-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-222-lcm (a b)
  (if (and (natp a) (natp b))
      (if (or (equal a 0) (equal b 0))
          0
        (/ (* a b) (mathd-numbertheory-222-gcd a b)))
    0))

(defun mathd-numbertheory-222-statement (b)
  (implies
   (and (natp b)
        (equal (mathd-numbertheory-222-lcm 120 b) 3720)
        (equal (mathd-numbertheory-222-gcd 120 b) 8))
   (equal b 248)))

(value-triple :itpeval-statement-checked)
:q
