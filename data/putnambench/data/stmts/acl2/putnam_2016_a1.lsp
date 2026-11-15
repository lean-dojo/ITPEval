;; Statement-only formalization of PutnamBench corpus artifact putnam_2016_a1:
;; the least positive derivative order for which every integer polynomial has
;; value divisible by 2016 at every integer input is 8. This file contains no
;; proof.

(in-package "ACL2")

;; Coefficients are listed in ascending degree order. Every integer polynomial
;; has such a finite coefficient list, so this is an exact representation of
;; the source polynomial type rather than a finite table of polynomial values.
(defun putnam-2016-a1-integer-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (integerp (car polynomial))
           (putnam-2016-a1-integer-polynomial-p
            (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-2016-a1-polynomial-value (polynomial x)
  (if (consp polynomial)
      (+ (car polynomial)
         (* x
            (putnam-2016-a1-polynomial-value
             (cdr polynomial) x)))
    0))

(defun putnam-2016-a1-derivative-aux
    (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (putnam-2016-a1-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun putnam-2016-a1-derivative (polynomial)
  (if (consp polynomial)
      (putnam-2016-a1-derivative-aux
       (cdr polynomial) 1)
    nil))

(defun putnam-2016-a1-iterated-derivative
    (polynomial order)
  (declare (xargs :measure (nfix order)))
  (if (zp order)
      polynomial
    (putnam-2016-a1-iterated-derivative
     (putnam-2016-a1-derivative polynomial)
     (- order 1))))

(defun putnam-2016-a1-divisible-value-p
    (polynomial order x)
  (equal
   (mod
    (putnam-2016-a1-polynomial-value
     (putnam-2016-a1-iterated-derivative
      polynomial order)
     x)
    2016)
   0))

(defun putnam-2016-a1-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-2016-a1-zero-list (- count 1)))))

;; This coefficient list denotes x^order. Its order-th derivative at zero is
;; order!, providing an internal counterexample for each order from 1 to 7.
(defun putnam-2016-a1-monomial-witness (order)
  (append (putnam-2016-a1-zero-list order)
          (list 1)))

(defun putnam-2016-a1-lower-orders-fail-p (order)
  (declare (xargs :measure (nfix order)))
  (if (zp order)
      t
    (and
     (not
      (putnam-2016-a1-divisible-value-p
       (putnam-2016-a1-monomial-witness order)
       order
       0))
     (putnam-2016-a1-lower-orders-fail-p
      (- order 1)))))

(defun putnam-2016-a1-solution ()
  8)

;; Universal closure over POLYNOMIAL and K is the source's quantification over
;; every integer polynomial and integer evaluation point. Since the solution
;; is 8, the explicit counterexamples for orders 1 through 7 are exactly the
;; lower-bound half of IsLeast.
(defun putnambench-putnam-2016-a1-statement
    (polynomial k)
  (and
   (putnam-2016-a1-lower-orders-fail-p
    (- (putnam-2016-a1-solution) 1))
   (implies
    (and
     (putnam-2016-a1-integer-polynomial-p polynomial)
     (integerp k))
    (putnam-2016-a1-divisible-value-p
     polynomial
     (putnam-2016-a1-solution)
     k))))

(value-triple :itpeval-statement-checked)
:q
