;; Statement-only formalization of PutnamBench corpus artifact putnam_1976_b5:
;; for every natural n, the alternating binomial sum of the polynomials
;; (X-k)^n is the constant polynomial n!. This file contains no proof.

(in-package "ACL2")

;; Coefficient vectors are listed from degree n down through degree zero.
;; The coefficient of X^degree in (X-k)^n is
;;
;;   choose(n, degree) * (-k)^(n-degree).
;;
;; Thus the left vector below is exactly the coefficient vector of the
;; source sum. Equality with the constant-polynomial vector is equivalent to
;; equality in Z[X]. Evaluating equal integer polynomials gives the source
;; identity for every real X; conversely, equality for every real X forces
;; equality of all coefficients. This encoding therefore preserves the real
;; function statement without restricting X to ACL2's rational numbers.

(defun putnam-1976-b5-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1976-b5-factorial (- n 1)))))

(defun putnam-1976-b5-binomial (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1976-b5-binomial (- n 1) k)
       (putnam-1976-b5-binomial
        (- n 1) (- k 1)))))

(defun putnam-1976-b5-coefficient-sum-through
    (n degree k)
  (declare (xargs :measure (nfix k)))
  (let ((term
         (* (expt -1 k)
            (putnam-1976-b5-binomial n k)
            (putnam-1976-b5-binomial n degree)
            (expt (- k) (- n degree)))))
    (if (zp k)
        term
      (+ (putnam-1976-b5-coefficient-sum-through
          n degree (- k 1))
         term))))

(defun putnam-1976-b5-left-coefficients (n degree)
  (declare (xargs :measure (nfix degree)))
  (if (zp degree)
      (list
       (putnam-1976-b5-coefficient-sum-through
        n 0 n))
    (cons
     (putnam-1976-b5-coefficient-sum-through
      n degree n)
     (putnam-1976-b5-left-coefficients
      n (- degree 1)))))

(defun putnam-1976-b5-constant-coefficients (n degree)
  (declare (xargs :measure (nfix degree)))
  (if (zp degree)
      (list (putnam-1976-b5-factorial n))
    (cons 0
          (putnam-1976-b5-constant-coefficients
           n (- degree 1)))))

(defun putnambench-putnam-1976-b5-statement (n)
  (implies
   (natp n)
   (equal
    (putnam-1976-b5-left-coefficients n n)
    (putnam-1976-b5-constant-coefficients n n))))

(value-triple :itpeval-statement-checked)
:q
