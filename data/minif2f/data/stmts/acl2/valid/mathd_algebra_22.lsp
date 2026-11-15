;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_22:
;; the base-5^2 logarithm of 5^4 equals 2. The logarithm quotient is
;; represented exactly as Laurent monomials in ln(5). This file contains no
;; proof.

(in-package "ACL2")

;; A pair (c . e) denotes the real number c * ln(5)^e.
(defun mathd-algebra-22-ln5-monomial (coefficient exponent)
  (cons coefficient exponent))

(defun mathd-algebra-22-coefficient (monomial)
  (car monomial))

(defun mathd-algebra-22-exponent (monomial)
  (cdr monomial))

(defun mathd-algebra-22-divide (left right)
  (if (equal (mathd-algebra-22-coefficient right) 0)
      nil
    (mathd-algebra-22-ln5-monomial
     (/ (mathd-algebra-22-coefficient left)
        (mathd-algebra-22-coefficient right))
     (- (mathd-algebra-22-exponent left)
        (mathd-algebra-22-exponent right)))))

;; For positive n = 5^k, ln(n) = k * ln(5).
(defun mathd-algebra-22-natural-log-power-of-5 (n k)
  (if (and (natp k)
           (< 0 k)
           (equal n (expt 5 k)))
      (mathd-algebra-22-ln5-monomial k 1)
    nil))

(defun mathd-algebra-22-constant (value)
  (mathd-algebra-22-ln5-monomial value 0))

(defun mathd-algebra-22-statement ()
  (equal
   (mathd-algebra-22-divide
    (mathd-algebra-22-natural-log-power-of-5 (expt 5 4) 4)
    (mathd-algebra-22-natural-log-power-of-5 (expt 5 2) 2))
   (mathd-algebra-22-constant 2)))

(value-triple :itpeval-statement-checked)
:q
