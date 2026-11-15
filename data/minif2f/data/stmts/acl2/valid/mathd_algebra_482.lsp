;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_482:
;; two distinct natural primes that are roots of the real quadratic
;; f(x) = x^2 - 12*x + k force k = 35. This file contains no proof.
;;
;; The source identity determines f uniquely, so its two root hypotheses are
;; exactly the polynomial equations below. Conversely, any m, n, and k
;; satisfying these equations extend to the source function by defining
;; f(x) = x^2 - 12*x + k on every real x. Either root equation forces the
;; source real k to equal 12*m - m^2, an integer, so requiring rationalp in
;; ACL2 omits no satisfying source instance. Thus eliminating f and embedding
;; the remaining exact values in ACL2 rationals is bidirectionally equivalent
;; to the source statement.

(in-package "ACL2")

(defun mathd-algebra-482-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and (not (equal (mod number divisor) 0))
           (mathd-algebra-482-no-divisor-from-p
            number
            (+ divisor 1)))
    t))

(defun mathd-algebra-482-primep (number)
  (and (natp number)
       (< 1 number)
       (mathd-algebra-482-no-divisor-from-p number 2)))

(defun mathd-algebra-482-polynomial (x k)
  (+ (- (expt x 2)
        (* 12 x))
     k))

(defun mathd-algebra-482-statement (m n k)
  (implies
   (and (natp m)
        (natp n)
        (rationalp k)
        (mathd-algebra-482-primep m)
        (mathd-algebra-482-primep n)
        (not (equal m n))
        (equal (mathd-algebra-482-polynomial m k) 0)
        (equal (mathd-algebra-482-polynomial n k) 0))
   (equal k 35)))

(value-triple :itpeval-statement-checked)
:q
