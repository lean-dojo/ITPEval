;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_169: the greatest common divisor of 20 factorial and
;; 200000 equals 40000. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-169-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (mathd-numbertheory-169-factorial (- n 1)))))

(defun mathd-numbertheory-169-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-169-gcd a (- b a)))
            (t
             (mathd-numbertheory-169-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-169-statement ()
  (equal
   (mathd-numbertheory-169-gcd
    (mathd-numbertheory-169-factorial 20)
    200000)
   40000))

(value-triple :itpeval-statement-checked)
:q
