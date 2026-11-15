;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_277: natural numbers with greatest common divisor 6
;; and least common multiple 126 have sum at least 60. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-277-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-277-gcd a (- b a)))
            (t
             (mathd-numbertheory-277-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-277-lcm (a b)
  (if (and (natp a) (natp b))
      (if (or (equal a 0) (equal b 0))
          0
        (/ (* a b) (mathd-numbertheory-277-gcd a b)))
    0))

(defun mathd-numbertheory-277-statement (m n)
  (implies
   (and (natp m)
        (natp n)
        (equal (mathd-numbertheory-277-gcd m n) 6)
        (equal (mathd-numbertheory-277-lcm m n) 126))
   (<= 60 (+ m n))))

(value-triple :itpeval-statement-checked)
:q
