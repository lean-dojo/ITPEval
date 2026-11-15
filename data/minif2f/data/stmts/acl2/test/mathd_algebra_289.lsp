;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_289:
;; natural prime coefficients m and n and two distinct ordered natural roots
;; k and t of x^2 - m*x + n determine the stated exponential sum. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-algebra-289-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and (not (equal (mod number divisor) 0))
           (mathd-algebra-289-no-divisor-from-p
            number
            (+ divisor 1)))
    t))

(defun mathd-algebra-289-primep (number)
  (and (natp number)
       (< 1 number)
       (mathd-algebra-289-no-divisor-from-p number 2)))

(defun mathd-algebra-289-statement (k root-t m n)
  (implies
   (and (natp k)
        (natp root-t)
        (natp m)
        (natp n)
        (mathd-algebra-289-primep m)
        (mathd-algebra-289-primep n)
        (< root-t k)
        (equal (+ (- (expt k 2) (* m k)) n) 0)
        (equal (+ (- (expt root-t 2) (* m root-t)) n) 0))
   (equal (+ (+ (+ (expt m n)
                   (expt n m))
                (expt k root-t))
             (expt root-t k))
          20)))

(value-triple :itpeval-statement-checked)
:q
