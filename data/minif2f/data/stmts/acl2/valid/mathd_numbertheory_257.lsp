;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_257: a natural number x between 1 and 100 for which
;; 77 divides the sum from 0 through 100 minus x must equal 45. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-257-sum-range (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (mathd-numbertheory-257-sum-range (- n 1))
       (- n 1))))

(defun mathd-numbertheory-257-statement (x)
  (implies
   (and (natp x)
        (<= 1 x)
        (<= x 100)
        (equal
         (mod
          (nfix
           (- (mathd-numbertheory-257-sum-range 101)
              x))
          77)
         0))
   (equal x 45)))

(value-triple :itpeval-statement-checked)
:q
