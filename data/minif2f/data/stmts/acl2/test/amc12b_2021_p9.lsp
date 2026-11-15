;; Statement-only formalization of miniF2F corpus artifact amc12b_2021_p9:
;; a real natural-logarithm identity whose nested quotient difference equals
;; 2. The fixed logarithms are represented exactly as rational functions in
;; symbolic generators ln(2) and ln(5). This file contains no proof.

(in-package "ACL2")

;; A term (c e2 e5) denotes c * ln(2)^e2 * ln(5)^e5. Polynomials are
;; canonical lists of terms ordered lexicographically by (e2,e5).
(defun amc12b-2021-p9-term
    (coefficient ln2-exponent ln5-exponent)
  (list coefficient ln2-exponent ln5-exponent))

(defun amc12b-2021-p9-term-coefficient (term)
  (nth 0 term))

(defun amc12b-2021-p9-term-ln2-exponent (term)
  (nth 1 term))

(defun amc12b-2021-p9-term-ln5-exponent (term)
  (nth 2 term))

(defun amc12b-2021-p9-same-monomial-p (left right)
  (and
   (equal
    (amc12b-2021-p9-term-ln2-exponent left)
    (amc12b-2021-p9-term-ln2-exponent right))
   (equal
    (amc12b-2021-p9-term-ln5-exponent left)
    (amc12b-2021-p9-term-ln5-exponent right))))

(defun amc12b-2021-p9-monomial-before-p (left right)
  (let ((left-ln2
         (amc12b-2021-p9-term-ln2-exponent left))
        (right-ln2
         (amc12b-2021-p9-term-ln2-exponent right))
        (left-ln5
         (amc12b-2021-p9-term-ln5-exponent left))
        (right-ln5
         (amc12b-2021-p9-term-ln5-exponent right)))
    (or (< left-ln2 right-ln2)
        (and (equal left-ln2 right-ln2)
             (< left-ln5 right-ln5)))))

(defun amc12b-2021-p9-polynomial-insert (term polynomial)
  (cond
   ((equal
     (amc12b-2021-p9-term-coefficient term)
     0)
    polynomial)
   ((atom polynomial)
    (list term))
   ((amc12b-2021-p9-same-monomial-p
     term
     (car polynomial))
    (let ((coefficient
           (+
            (amc12b-2021-p9-term-coefficient term)
            (amc12b-2021-p9-term-coefficient
             (car polynomial)))))
      (if (equal coefficient 0)
          (cdr polynomial)
        (cons
         (amc12b-2021-p9-term
          coefficient
          (amc12b-2021-p9-term-ln2-exponent term)
          (amc12b-2021-p9-term-ln5-exponent term))
         (cdr polynomial)))))
   ((amc12b-2021-p9-monomial-before-p
     term
     (car polynomial))
    (cons term polynomial))
   (t
    (cons
     (car polynomial)
     (amc12b-2021-p9-polynomial-insert
      term
      (cdr polynomial))))))

(defun amc12b-2021-p9-polynomial-add (left right)
  (if (atom left)
      right
    (amc12b-2021-p9-polynomial-insert
     (car left)
     (amc12b-2021-p9-polynomial-add
      (cdr left)
      right))))

(defun amc12b-2021-p9-polynomial-negate (polynomial)
  (if (atom polynomial)
      nil
    (cons
     (amc12b-2021-p9-term
      (-
       (amc12b-2021-p9-term-coefficient
        (car polynomial)))
      (amc12b-2021-p9-term-ln2-exponent
       (car polynomial))
      (amc12b-2021-p9-term-ln5-exponent
       (car polynomial)))
     (amc12b-2021-p9-polynomial-negate
      (cdr polynomial)))))

(defun amc12b-2021-p9-polynomial-subtract (left right)
  (amc12b-2021-p9-polynomial-add
   left
   (amc12b-2021-p9-polynomial-negate right)))

(defun amc12b-2021-p9-term-multiply (left right)
  (amc12b-2021-p9-term
   (*
    (amc12b-2021-p9-term-coefficient left)
    (amc12b-2021-p9-term-coefficient right))
   (+
    (amc12b-2021-p9-term-ln2-exponent left)
    (amc12b-2021-p9-term-ln2-exponent right))
   (+
    (amc12b-2021-p9-term-ln5-exponent left)
    (amc12b-2021-p9-term-ln5-exponent right))))

(defun amc12b-2021-p9-term-times-polynomial (term polynomial)
  (if (atom polynomial)
      nil
    (amc12b-2021-p9-polynomial-insert
     (amc12b-2021-p9-term-multiply
      term
      (car polynomial))
     (amc12b-2021-p9-term-times-polynomial
      term
      (cdr polynomial)))))

(defun amc12b-2021-p9-polynomial-multiply (left right)
  (if (atom left)
      nil
    (amc12b-2021-p9-polynomial-add
     (amc12b-2021-p9-term-times-polynomial
      (car left)
      right)
     (amc12b-2021-p9-polynomial-multiply
      (cdr left)
      right))))

(defun amc12b-2021-p9-monomial
    (coefficient ln2-exponent ln5-exponent)
  (if (equal coefficient 0)
      nil
    (list
     (amc12b-2021-p9-term
      coefficient
      ln2-exponent
      ln5-exponent))))

(defun amc12b-2021-p9-polynomial-constant (value)
  (amc12b-2021-p9-monomial value 0 0))

;; Since 20=2^2*5, 40=2^3*5, 80=2^4*5, and 160=2^5*5,
;; these are the exact additive coordinates of the source logarithms.
(defun amc12b-2021-p9-natural-log-coordinate (n)
  (cond
   ((equal n 2)
    (amc12b-2021-p9-monomial 1 1 0))
   ((equal n 20)
    (amc12b-2021-p9-polynomial-add
     (amc12b-2021-p9-monomial 2 1 0)
     (amc12b-2021-p9-monomial 1 0 1)))
   ((equal n 40)
    (amc12b-2021-p9-polynomial-add
     (amc12b-2021-p9-monomial 3 1 0)
     (amc12b-2021-p9-monomial 1 0 1)))
   ((equal n 80)
    (amc12b-2021-p9-polynomial-add
     (amc12b-2021-p9-monomial 4 1 0)
     (amc12b-2021-p9-monomial 1 0 1)))
   ((equal n 160)
    (amc12b-2021-p9-polynomial-add
     (amc12b-2021-p9-monomial 5 1 0)
     (amc12b-2021-p9-monomial 1 0 1)))
   (t nil)))

;; A rational function is (numerator denominator), with both entries
;; canonical polynomials. Every divisor constructed below is nonzero because
;; it denotes a natural logarithm of a real number greater than 1.
(defun amc12b-2021-p9-rational-function
    (numerator denominator)
  (list numerator denominator))

(defun amc12b-2021-p9-rational-function-numerator
    (function)
  (nth 0 function))

(defun amc12b-2021-p9-rational-function-denominator
    (function)
  (nth 1 function))

(defun amc12b-2021-p9-rational-function-from-polynomial
    (polynomial)
  (amc12b-2021-p9-rational-function
   polynomial
   (amc12b-2021-p9-polynomial-constant 1)))

(defun amc12b-2021-p9-rational-function-constant (value)
  (amc12b-2021-p9-rational-function-from-polynomial
   (amc12b-2021-p9-polynomial-constant value)))

(defun amc12b-2021-p9-rational-function-divide (left right)
  (amc12b-2021-p9-rational-function
   (amc12b-2021-p9-polynomial-multiply
    (amc12b-2021-p9-rational-function-numerator left)
    (amc12b-2021-p9-rational-function-denominator right))
   (amc12b-2021-p9-polynomial-multiply
    (amc12b-2021-p9-rational-function-denominator left)
    (amc12b-2021-p9-rational-function-numerator right))))

(defun amc12b-2021-p9-rational-function-subtract (left right)
  (amc12b-2021-p9-rational-function
   (amc12b-2021-p9-polynomial-subtract
    (amc12b-2021-p9-polynomial-multiply
     (amc12b-2021-p9-rational-function-numerator left)
     (amc12b-2021-p9-rational-function-denominator right))
    (amc12b-2021-p9-polynomial-multiply
     (amc12b-2021-p9-rational-function-numerator right)
     (amc12b-2021-p9-rational-function-denominator left)))
   (amc12b-2021-p9-polynomial-multiply
    (amc12b-2021-p9-rational-function-denominator left)
    (amc12b-2021-p9-rational-function-denominator right))))

(defun amc12b-2021-p9-rational-function-equal (left right)
  (equal
   (amc12b-2021-p9-polynomial-multiply
    (amc12b-2021-p9-rational-function-numerator left)
    (amc12b-2021-p9-rational-function-denominator right))
   (amc12b-2021-p9-polynomial-multiply
    (amc12b-2021-p9-rational-function-numerator right)
    (amc12b-2021-p9-rational-function-denominator left))))

(defun amc12b-2021-p9-logarithm (n)
  (amc12b-2021-p9-rational-function-from-polynomial
   (amc12b-2021-p9-natural-log-coordinate n)))

(defun amc12b-2021-p9-statement ()
  (let* ((ln80 (amc12b-2021-p9-logarithm 80))
         (ln2 (amc12b-2021-p9-logarithm 2))
         (ln40 (amc12b-2021-p9-logarithm 40))
         (ln160 (amc12b-2021-p9-logarithm 160))
         (ln20 (amc12b-2021-p9-logarithm 20))
         (first-term
          (amc12b-2021-p9-rational-function-divide
           (amc12b-2021-p9-rational-function-divide
            ln80
            ln2)
           (amc12b-2021-p9-rational-function-divide
            ln2
            ln40)))
         (second-term
          (amc12b-2021-p9-rational-function-divide
           (amc12b-2021-p9-rational-function-divide
            ln160
            ln2)
           (amc12b-2021-p9-rational-function-divide
            ln2
            ln20))))
    (amc12b-2021-p9-rational-function-equal
     (amc12b-2021-p9-rational-function-subtract
      first-term
      second-term)
     (amc12b-2021-p9-rational-function-constant 2))))

(value-triple :itpeval-statement-checked)
:q
