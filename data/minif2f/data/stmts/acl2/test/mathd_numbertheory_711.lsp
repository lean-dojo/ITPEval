;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_711: positive natural numbers with greatest common
;; divisor 8 and least common multiple 112 have sum at least 72.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-711-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-711-gcd a (- b a)))
            (t
             (mathd-numbertheory-711-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-711-lcm (a b)
  (if (and (natp a) (natp b))
      (if (or (equal a 0) (equal b 0))
          0
        (/ (* a b) (mathd-numbertheory-711-gcd a b)))
    0))

(defun mathd-numbertheory-711-statement (m n)
  (implies
   (and (natp m)
        (natp n)
        (< 0 m)
        (< 0 n)
        (equal (mathd-numbertheory-711-gcd m n) 8)
        (equal (mathd-numbertheory-711-lcm m n) 112))
   (<= 72 (+ m n))))

(value-triple :itpeval-statement-checked)
:q
