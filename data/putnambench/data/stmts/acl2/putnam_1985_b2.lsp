;; Statement-only formalization of PutnamBench corpus artifact putnam_1985_b2:
;; the prime factorization of f_100(1) for the recursively differentiated
;; polynomial sequence is 101^99. This file contains no proof.

(in-package "ACL2")

;; Formal polynomials are coefficient lists in ascending degree order.
;; ACL2's exact rationals contain the natural coefficients of the source
;; polynomials, and equality of these lists is equality of formal polynomials.
(defun putnam-1985-b2-polynomial-add (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons (+ (car left) (car right))
          (putnam-1985-b2-polynomial-add
           (cdr left) (cdr right))))))

(defun putnam-1985-b2-polynomial-scale (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons (* scalar (car polynomial))
          (putnam-1985-b2-polynomial-scale
           scalar (cdr polynomial)))))

;; With PREVIOUS initially zero, this multiplies a polynomial by X+1.
(defun putnam-1985-b2-multiply-x-plus-one
    (polynomial previous)
  (if (consp polynomial)
      (cons (+ (car polynomial) previous)
            (putnam-1985-b2-multiply-x-plus-one
             (cdr polynomial) (car polynomial)))
    (if (equal previous 0)
        nil
      (list previous))))

;; Horner recursion computes p(X+1) as a formal polynomial.
(defun putnam-1985-b2-compose-shift-one (polynomial)
  (if (consp polynomial)
      (putnam-1985-b2-polynomial-add
       (list (car polynomial))
       (putnam-1985-b2-multiply-x-plus-one
        (putnam-1985-b2-compose-shift-one (cdr polynomial))
        0))
    nil))

(defun putnam-1985-b2-antiderivative-coefficients
    (polynomial divisor)
  (if (consp polynomial)
      (cons (/ (car polynomial) divisor)
            (putnam-1985-b2-antiderivative-coefficients
             (cdr polynomial) (+ divisor 1)))
    nil))

;; This is the unique formal antiderivative with constant coefficient zero.
(defun putnam-1985-b2-antiderivative-zero (polynomial)
  (cons
   0
   (putnam-1985-b2-antiderivative-coefficients polynomial 1)))

;; The source hypotheses uniquely determine this sequence: f_0=1, and for
;; n>0, f_n has zero constant coefficient and derivative
;; n*f_(n-1)(X+1). Conversely these definitions satisfy exactly those
;; hypotheses, so eliminating the external sequence parameter is
;; bidirectionally equivalent.
(defun putnam-1985-b2-polynomial (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n)) (zp n))
      (list 1)
    (putnam-1985-b2-antiderivative-zero
     (putnam-1985-b2-polynomial-scale
      n
      (putnam-1985-b2-compose-shift-one
       (putnam-1985-b2-polynomial (- n 1)))))))

(defun putnam-1985-b2-polynomial-evaluate (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value
            (putnam-1985-b2-polynomial-evaluate
             (cdr polynomial) value)))
    0))

(defun putnam-1985-b2-no-divisor-from-p (n divisor)
  (declare (xargs :measure (nfix (- n divisor))))
  (if (and (natp n)
           (natp divisor)
           (<= 2 divisor)
           (< divisor n))
      (and
       (not (equal (mod n divisor) 0))
       (putnam-1985-b2-no-divisor-from-p n (+ divisor 1)))
    t))

(defun putnam-1985-b2-primep (n)
  (and (natp n)
       (< 1 n)
       (putnam-1985-b2-no-divisor-from-p n 2)))

;; Since 101 is prime, equality with 101^99 is equivalent by unique prime
;; factorization to exponent 99 at 101 and exponent zero at every other prime.
(defun putnambench-putnam-1985-b2-statement ()
  (and
   (putnam-1985-b2-primep 101)
   (equal
    (putnam-1985-b2-polynomial-evaluate
     (putnam-1985-b2-polynomial 100)
     1)
    (expt 101 99))))

(value-triple :itpeval-statement-checked)
:q
