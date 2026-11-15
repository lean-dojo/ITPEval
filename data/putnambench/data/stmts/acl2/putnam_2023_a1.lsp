;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_a1:
;; the least positive n for which the second derivative at zero of
;; product_{i=1}^n cos(i*x) has absolute value greater than 2023 is 18.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A pair (a . b) represents the exact degree-two even Taylor jet
;; a + b*x^2.  Since cos(i*x) = 1 - i^2*x^2/2 + O(x^4), multiplying these
;; jets gives the constant and quadratic coefficients of the full cosine
;; product exactly.  Its second derivative at zero is twice the quadratic
;; coefficient.  Thus this finite jet is an exact representation of the
;; derivative queried by the source statement, not a finite sampling or a
;; restriction of the real domain.

(defun putnam-2023-a1-cosine-two-jet (index)
  (cons 1
        (- (/ (* index index) 2))))

(defun putnam-2023-a1-multiply-two-jets (left right)
  (let ((left-constant (car left))
        (left-quadratic (cdr left))
        (right-constant (car right))
        (right-quadratic (cdr right)))
    (cons
     (* left-constant right-constant)
     (+ (* left-constant right-quadratic)
        (* left-quadratic right-constant)))))

(defun putnam-2023-a1-product-two-jet (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons 1 0)
    (putnam-2023-a1-multiply-two-jets
     (putnam-2023-a1-product-two-jet (- n 1))
     (putnam-2023-a1-cosine-two-jet n))))

(defun putnam-2023-a1-second-derivative-at-zero (n)
  (* 2
     (cdr (putnam-2023-a1-product-two-jet n))))

(defun putnam-2023-a1-solution ()
  18)

(defun putnambench-putnam-2023-a1-statement (n)
  (let ((solution (putnam-2023-a1-solution)))
    (and
     (posp solution)
     (< 2023
        (abs
         (putnam-2023-a1-second-derivative-at-zero
          solution)))
     (implies
      (and
       (natp n)
       (< 0 n)
       (< n solution))
      (<=
       (abs
        (putnam-2023-a1-second-derivative-at-zero n))
       2023)))))

(value-triple :itpeval-statement-checked)
:q
