;; Statement-only formalization of PutnamBench corpus artifact putnam_1975_a4:
;; for odd natural m greater than 1 and theta = exp(2*pi*i/(2m)), the inverse
;; of 1-theta is the integer polynomial sum of the odd powers of theta below
;; degree m-1. This file contains no proof.

(in-package "ACL2")

;; Let theta = exp(pi*i/m), a primitive (2m)-th root of unity. For
;;
;;   S_m(X) = X + X^3 + ... + X^(m-2),
;;
;; the source equality 1/(1-theta) = S_m(theta) is equivalent, since
;; theta is not 1, to ((1-X)S_m(X)-1)(theta) = 0. The minimal polynomial of
;; theta over the rationals is Phi_(2m), so this vanishing condition is
;; bidirectionally equivalent to divisibility by Phi_(2m). Polynomials below
;; use rational coefficient lists in ascending degree order.

(defun putnam-1975-a4-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-1975-a4-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-1975-a4-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-1975-a4-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-1975-a4-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1975-a4-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun putnam-1975-a4-poly-negate (polynomial)
  (putnam-1975-a4-poly-scale -1 polynomial))

(defun putnam-1975-a4-poly-subtract (left right)
  (putnam-1975-a4-poly-normalize
   (putnam-1975-a4-poly-add
    left
    (putnam-1975-a4-poly-negate right))))

(defun putnam-1975-a4-poly-multiply (left right)
  (if (consp left)
      (putnam-1975-a4-poly-normalize
       (putnam-1975-a4-poly-add
        (putnam-1975-a4-poly-scale (car left) right)
        (cons 0
              (putnam-1975-a4-poly-multiply
               (cdr left) right))))
    nil))

(defun putnam-1975-a4-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-1975-a4-zero-list (- count 1)))))

(defun putnam-1975-a4-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (putnam-1975-a4-zero-list degree)
     (list coefficient))))

(defun putnam-1975-a4-poly-degree (polynomial)
  (let ((normalized
         (putnam-1975-a4-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun putnam-1975-a4-poly-leading-coefficient (polynomial)
  (let ((normalized
         (putnam-1975-a4-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (putnam-1975-a4-poly-degree normalized)
             normalized)
      0)))

;; The step bound exceeds the number of degree reductions required by
;; polynomial long division with a nonzero divisor.
(defun putnam-1975-a4-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons (putnam-1975-a4-poly-normalize quotient)
            (putnam-1975-a4-poly-normalize remainder))
    (let* ((normalized-remainder
            (putnam-1975-a4-poly-normalize remainder))
           (normalized-divisor
            (putnam-1975-a4-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (putnam-1975-a4-poly-degree
                  normalized-remainder)
                 (putnam-1975-a4-poly-degree
                  normalized-divisor)))
          (cons (putnam-1975-a4-poly-normalize quotient)
                normalized-remainder)
        (let* ((degree-difference
                (- (putnam-1975-a4-poly-degree
                    normalized-remainder)
                   (putnam-1975-a4-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (putnam-1975-a4-poly-leading-coefficient
                    normalized-remainder)
                   (putnam-1975-a4-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (putnam-1975-a4-poly-monomial
                 coefficient degree-difference)))
          (putnam-1975-a4-poly-divmod-steps
           (putnam-1975-a4-poly-subtract
            normalized-remainder
            (putnam-1975-a4-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (putnam-1975-a4-poly-add quotient term)
           (- steps 1)))))))

(defun putnam-1975-a4-poly-divmod (dividend divisor)
  (putnam-1975-a4-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1
      (len (putnam-1975-a4-poly-normalize dividend)))))

(defun putnam-1975-a4-poly-quotient (dividend divisor)
  (car (putnam-1975-a4-poly-divmod dividend divisor)))

(defun putnam-1975-a4-poly-remainder (dividend divisor)
  (cdr (putnam-1975-a4-poly-divmod dividend divisor)))

(defun putnam-1975-a4-x-to-n-minus-one (n)
  (putnam-1975-a4-poly-add
   (list -1)
   (putnam-1975-a4-poly-monomial 1 n)))

;; The list PRECEDING contains Phi_1 through Phi_(n-1).
(defun putnam-1975-a4-proper-divisor-product
    (n divisor preceding)
  (declare (xargs :measure (nfix divisor)))
  (if (zp divisor)
      (list 1)
    (let ((remaining
           (putnam-1975-a4-proper-divisor-product
            n (- divisor 1) preceding)))
      (if (equal (mod n divisor) 0)
          (putnam-1975-a4-poly-multiply
           (nth (- divisor 1) preceding)
           remaining)
        remaining))))

;; Phi_n = (X^n - 1) / product_(d | n, d < n) Phi_d.
(defun putnam-1975-a4-cyclotomic-list (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (let* ((preceding
            (putnam-1975-a4-cyclotomic-list (- n 1)))
           (proper-divisor-product
            (putnam-1975-a4-proper-divisor-product
             n (- n 1) preceding))
           (phi-n
            (putnam-1975-a4-poly-quotient
             (putnam-1975-a4-x-to-n-minus-one n)
             proper-divisor-product)))
      (append
       preceding
       (list (putnam-1975-a4-poly-normalize phi-n))))))

(defun putnam-1975-a4-cyclotomic-polynomial (n)
  (if (zp n)
      nil
    (nth (- n 1)
         (putnam-1975-a4-cyclotomic-list n))))

(defun putnam-1975-a4-odd-power-sum (count exponent)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (putnam-1975-a4-poly-add
     (putnam-1975-a4-poly-monomial 1 exponent)
     (putnam-1975-a4-odd-power-sum
      (- count 1) (+ exponent 2)))))

(defun putnam-1975-a4-solution-polynomial (m)
  (putnam-1975-a4-odd-power-sum
   (floor (- m 1) 2)
   1))

(defun putnam-1975-a4-equation-polynomial (m)
  (putnam-1975-a4-poly-subtract
   (putnam-1975-a4-poly-multiply
    (list 1 -1)
    (putnam-1975-a4-solution-polynomial m))
   (list 1)))

(defun putnambench-putnam-1975-a4-statement (m)
  (implies
   (and (natp m)
        (< 1 m)
        (equal (mod m 2) 1))
   (equal
    (putnam-1975-a4-poly-remainder
     (putnam-1975-a4-equation-polynomial m)
     (putnam-1975-a4-cyclotomic-polynomial (* 2 m)))
    nil)))

(value-triple :itpeval-statement-checked)
:q
