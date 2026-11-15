;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_a3:
;; the base-2 logarithm of the double product of 1+exp(2*pi*i*a*b/2015)
;; for 1 <= a,b <= 2015 is 13725. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Let zeta = exp(2*pi*i/2015).  It is a primitive 2015th root of unity.
;; Replacing zeta by X turns the source product into
;;
;;   P(X) = product_(a=1)^2015 product_(b=1)^2015 (1+X^(a*b)).
;;
;; The dense coefficient calculation below works modulo X^2015-1, which
;; does not change the value at zeta.  Since Phi_2015 is the minimal
;; polynomial of zeta over the rationals,
;;
;;   P(zeta) = 2^13725
;;
;; holds exactly when Phi_2015 divides P(X)-2^13725.
;;
;; No factor 1+zeta^(a*b) vanishes: every power of zeta has odd order, so it
;; cannot equal -1.  The complete product is positive real (conjugate powers
;; pair, and the remaining powers equal 1).  Consequently the displayed
;; algebraic equality is bidirectionally equivalent to the source base-2
;; logarithm being 13725.  This exact cyclotomic encoding does not replace
;; complex values by ACL2's complex rationals.

;; General polynomials use rational coefficient lists in ascending degree
;; order.

(defun putnam-2015-a3-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-2015-a3-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-2015-a3-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-2015-a3-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-2015-a3-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-2015-a3-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun putnam-2015-a3-poly-negate (polynomial)
  (putnam-2015-a3-poly-scale -1 polynomial))

(defun putnam-2015-a3-poly-subtract (left right)
  (putnam-2015-a3-poly-normalize
   (putnam-2015-a3-poly-add
    left
    (putnam-2015-a3-poly-negate right))))

(defun putnam-2015-a3-poly-multiply (left right)
  (if (consp left)
      (putnam-2015-a3-poly-normalize
       (putnam-2015-a3-poly-add
        (putnam-2015-a3-poly-scale (car left) right)
        (cons 0
              (putnam-2015-a3-poly-multiply
               (cdr left) right))))
    nil))

(defun putnam-2015-a3-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-2015-a3-zero-list (- count 1)))))

(defun putnam-2015-a3-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (putnam-2015-a3-zero-list degree)
     (list coefficient))))

(defun putnam-2015-a3-poly-degree (polynomial)
  (let ((normalized
         (putnam-2015-a3-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun putnam-2015-a3-poly-leading-coefficient (polynomial)
  (let ((normalized
         (putnam-2015-a3-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (putnam-2015-a3-poly-degree normalized)
             normalized)
      0)))

(defun putnam-2015-a3-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons (putnam-2015-a3-poly-normalize quotient)
            (putnam-2015-a3-poly-normalize remainder))
    (let* ((normalized-remainder
            (putnam-2015-a3-poly-normalize remainder))
           (normalized-divisor
            (putnam-2015-a3-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (putnam-2015-a3-poly-degree
                  normalized-remainder)
                 (putnam-2015-a3-poly-degree
                  normalized-divisor)))
          (cons (putnam-2015-a3-poly-normalize quotient)
                normalized-remainder)
        (let* ((degree-difference
                (- (putnam-2015-a3-poly-degree
                    normalized-remainder)
                   (putnam-2015-a3-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (putnam-2015-a3-poly-leading-coefficient
                    normalized-remainder)
                   (putnam-2015-a3-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (putnam-2015-a3-poly-monomial
                 coefficient degree-difference)))
          (putnam-2015-a3-poly-divmod-steps
           (putnam-2015-a3-poly-subtract
            normalized-remainder
            (putnam-2015-a3-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (putnam-2015-a3-poly-add quotient term)
           (- steps 1)))))))

(defun putnam-2015-a3-poly-divmod (dividend divisor)
  (putnam-2015-a3-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1
      (len (putnam-2015-a3-poly-normalize dividend)))))

(defun putnam-2015-a3-poly-quotient (dividend divisor)
  (car (putnam-2015-a3-poly-divmod dividend divisor)))

(defun putnam-2015-a3-poly-remainder (dividend divisor)
  (cdr (putnam-2015-a3-poly-divmod dividend divisor)))

(defun putnam-2015-a3-x-to-n-minus-one (n)
  (putnam-2015-a3-poly-add
   (list -1)
   (putnam-2015-a3-poly-monomial 1 n)))

;; Since 2015 = 5*13*31 is square-free,
;;
;; Phi_2015(X)
;;   = ((X^2015-1)(X^5-1)(X^13-1)(X^31-1))
;;       / ((X-1)(X^65-1)(X^155-1)(X^403-1)).
(defun putnam-2015-a3-cyclotomic-polynomial ()
  (putnam-2015-a3-poly-quotient
   (putnam-2015-a3-poly-multiply
    (putnam-2015-a3-x-to-n-minus-one 2015)
    (putnam-2015-a3-poly-multiply
     (putnam-2015-a3-x-to-n-minus-one 5)
     (putnam-2015-a3-poly-multiply
      (putnam-2015-a3-x-to-n-minus-one 13)
      (putnam-2015-a3-x-to-n-minus-one 31))))
   (putnam-2015-a3-poly-multiply
    (putnam-2015-a3-x-to-n-minus-one 1)
    (putnam-2015-a3-poly-multiply
     (putnam-2015-a3-x-to-n-minus-one 65)
     (putnam-2015-a3-poly-multiply
      (putnam-2015-a3-x-to-n-minus-one 155)
      (putnam-2015-a3-x-to-n-minus-one 403))))))

;; A degree-below-N coefficient list represents a polynomial modulo X^N-1.
;; Multiplication by 1+X^EXPONENT adds each coefficient to the coefficient
;; cyclically EXPONENT places ahead.
(defun putnam-2015-a3-factor-coefficients
    (polynomial exponent modulus index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (+ (nth index polynomial)
        (nth (mod (- index exponent) modulus)
             polynomial))
     (putnam-2015-a3-factor-coefficients
      polynomial exponent modulus (+ index 1)
      (- remaining 1)))))

(defun putnam-2015-a3-multiply-factor
    (polynomial exponent modulus)
  (if (posp modulus)
      (putnam-2015-a3-factor-coefficients
       polynomial
       (mod exponent modulus)
       modulus
       0
       modulus)
    nil))

(defun putnam-2015-a3-inner-product
    (a b modulus polynomial)
  (declare (xargs :measure (nfix b)))
  (if (zp b)
      polynomial
    (putnam-2015-a3-inner-product
     a
     (- b 1)
     modulus
     (putnam-2015-a3-multiply-factor
      polynomial (* a b) modulus))))

(defun putnam-2015-a3-double-product
    (a modulus polynomial)
  (declare (xargs :measure (nfix a)))
  (if (zp a)
      polynomial
    (putnam-2015-a3-double-product
     (- a 1)
     modulus
     (putnam-2015-a3-inner-product
      a modulus modulus polynomial))))

(defun putnam-2015-a3-product-polynomial ()
  (putnam-2015-a3-double-product
   2015
   2015
   (cons 1 (putnam-2015-a3-zero-list 2014))))

(defun putnam-2015-a3-equation-polynomial ()
  (putnam-2015-a3-poly-subtract
   (putnam-2015-a3-product-polynomial)
   (list (expt 2 13725))))

(defun putnambench-putnam-2015-a3-statement ()
  (equal
   (putnam-2015-a3-poly-remainder
    (putnam-2015-a3-equation-polynomial)
    (putnam-2015-a3-cyclotomic-polynomial))
   nil))

(value-triple :itpeval-statement-checked)
:q
